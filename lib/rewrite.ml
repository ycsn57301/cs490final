open Ast

exception UndefinedFun of string

(* Low priority TODO: should better implement it without using side effect *)
(** Extract all user-defined function calls out of expressions *)
type funext_env =
  {
    funext_counter : int ref;
    funext_funs : (string, funsig) Hashtbl.t;
    funext_anno_calls : p_cmd_node list ref; (* reversed order *)
  }

let new_anno_var env =
  let r_num = !(env.funext_counter) in
  env.funext_counter := !(env.funext_counter) + 1;
  "OU_anno_r"^string_of_int r_num

let append_anno_call env f pe =
  let f_sig =
    try Hashtbl.find env.funext_funs f
    with Not_found -> raise (UndefinedFun f)
  in
  (* create anonymous receiver *)
  let ty_ret = f_sig.funsig_return in
  let r = new_anno_var env in
  (* construct definition command *)
  let pc = mk_p_cmd (PCdef (ty_ret, r, pe)) (loc_of_p_expr pe) in
  (* add to history *)
  env.funext_anno_calls := pc :: !(env.funext_anno_calls);
  (* construct lexpr *)
  mk_p_expr (PEvar r) (loc_of_p_expr pe)

let rec extract_expr env pe =
  let ret pe' = mk_p_expr pe' (loc_of_p_expr pe) in
  match pe.p_expr with
  | PEunit | PEbool _ | PEint _ | PEfloat _ | PEnull -> pe
  | PEref ple ->
    let ple' = extract_expr env ple in
    ret (PEref ple')
  | PEcall (f, pe_args) ->
    let pe_args' = List.map (extract_expr env) pe_args in
    let pe' = ret (PEcall (f, pe_args')) in
    begin match f with
    | "reveal" | "print" | "commit" | "debug0" | "debug1" -> pe'
    | _ when Hashtbl.mem Builtin.builtin_types f -> (* builtin *)
      pe'
    | _ -> (* user-defined function call *)
      let ple = append_anno_call env f pe' in
      ple
    end
  | PEarrayinit pe_inits ->
    let pe_inits' = List.map (extract_expr env) pe_inits in
    ret (PEarrayinit pe_inits')
  | PEstructinit pe_asgns ->
    let pe_asgns' = List.map (fun (field, pe_asgn) ->
      field, extract_expr env pe_asgn) pe_asgns in
    ret (PEstructinit pe_asgns')
  | PEbinary (pe1, op, pe2) ->
    let pe1' = extract_expr env pe1 in
    let pe2' = extract_expr env pe2 in
    ret (PEbinary (pe1', op, pe2'))
  | PEunary (op, pe1) ->
    let pe1' = extract_expr env pe1 in
    ret (PEunary (op, pe1'))
  | PEvar _ -> pe
  | PEindex (ple_arr, pe_index) ->
    let ple_arr' = extract_expr env ple_arr in
    let pe_index' = extract_expr env pe_index in
    ret (PEindex (ple_arr', pe_index'))
  | PEfield (ple_st, field) ->
    let ple_st' = extract_expr env ple_st in
    ret (PEfield (ple_st', field))
  | PEderef pe1 ->
    let pe1' = extract_expr env pe1 in
    ret (PEderef pe1')

let rec extract_cmd env pc =
  let ret pc' =
    (* collect all anno calls from the env, and append pc' to the end *)
    let new_pc = mk_p_cmd pc' (loc_of_p_cmd pc) in
    let res = List.fold_left (fun tail call ->
      mk_p_cmd (PCseq (call, tail)) (loc_of_p_cmd tail))
      new_pc !(env.funext_anno_calls)
    in
    (* clear history *)
    env.funext_anno_calls := [];
    res
  in
  match pc.p_cmd with
  | PCskip | PCbreak | PCcontinue -> pc
  | PCseq (pc1, pc2) ->
    ret (PCseq (extract_cmd env pc1, extract_cmd env pc2))
  | PCdef (ty, x, pe) ->
    begin match pe.p_expr with
    | PEcall (f, pe_args) -> (* no need to extract the call out as it is already assigned to a variable *)
      let pe_args' = List.map (extract_expr env) pe_args in
      let pe' = mk_p_expr (PEcall (f, pe_args')) (loc_of_p_expr pe) in
      ret (PCdef (ty, x, pe'))
    | _ ->
      let pe' = extract_expr env pe in
      ret (PCdef (ty, x, pe'))
    end
  | PCasgn (ple, pe) ->
    let ple' = extract_expr env ple in
    let pe' = extract_expr env pe in
    ret (PCasgn (ple', pe'))
  | PCeval pe ->
    let x = new_anno_var env in
    let pc_def = mk_p_cmd (PCdef (Tunit, x, pe)) (loc_of_p_cmd pc) in
    extract_cmd env pc_def
  | PCif (pe, pc1, pc2) ->
    (* call extract_expr in the end, otherwise its anno calls will be merged into pc1' *)
    let pc1' = extract_cmd env pc1 in
    let pc2' = extract_cmd env pc2 in
    let pe' = extract_expr env pe in
    ret (PCif (pe', pc1', pc2'))
  | PCfor _ -> raise (Failure "PCfor should have been rewritten into PCwhile")
  | PCwhile (pe, pc1) ->
    let pc1' = extract_cmd env pc1 in
    let pe' = extract_expr env pe in
    ret (PCwhile (pe', pc1'))
  | PCsection pc1 -> ret (PCsection (extract_cmd env pc1))
  | PCreturn pe ->
    let pe' = extract_expr env pe in
    ret (PCreturn pe')
  | PCassert pe ->
    let pe' = extract_expr env pe in
    ret (PCassert pe')

(** Rewrite a command by extracting all user-defined function calls out of expressions.
    This should only rewrite function bodies as the anno variable counter is
    reset every time the function is called. *)
let extract_funcall sigs body =
  let env = {
    funext_counter = ref 0;
    funext_funs = sigs;
    funext_anno_calls = ref [];
  } in
  extract_cmd env body

let rewrite_for_to_while pc =
  let rec rewrite pc =
    let ret pc' = mk_p_cmd pc' (loc_of_p_cmd pc) in
    match pc.p_cmd with
    | PCskip | PCdef _ | PCasgn _ | PCeval _ | PCreturn _
    | PCbreak | PCcontinue | PCassert _ -> pc
    | PCseq (pc1, pc2) ->
      ret (PCseq (rewrite pc1, rewrite pc2))
    | PCif (e, pc1, pc2) ->
      ret (PCif (e, rewrite pc1, rewrite pc2))
    | PCfor (init, check, step, body) ->
      let new_body = rewrite body in
      let loop_body = mk_p_cmd (PCseq (new_body, step)) (loc_of_p_cmd body) in
      let loop_section = mk_p_cmd (PCsection loop_body) (loc_of_p_cmd body) in
      let loop = mk_p_cmd (PCwhile (check, loop_section)) (loc_of_p_cmd body) in
      let init_and_loop = mk_p_cmd (PCseq (init, loop)) (loc_of_p_cmd pc) in
      ret (PCsection init_and_loop)
    | PCwhile (e, pc1) ->
      ret (PCwhile (e, rewrite pc1))
    | PCsection pc1 ->
      ret (PCsection (rewrite pc1))
  in
  rewrite pc

(*
(** If a return variable, e.g. f$r0, is immediately stored into another variable,
    then delete f$r0. For instance:
    pvt int f$r0 = ...; receiver$0 = f$r0;
    will be merged into:
    receiver$0 = ...; *)
let optimize_return_variables sprog_rev =
  let rec merge_ret_def sprog_rev =
    match sprog_rev with
    | (sc2, cost2) :: (sc1, cost1) :: blocks' ->
      begin match sc1.scmd with
      | SCdef (_, alias, se) when is_return_alias alias ->
        begin match sc2.scmd with
        (* pvt int f$r0 = ...; pvt int var = f$r0; -> pvt int var = ...; *)
        | SCdef (ty, var, { sexpr = SElexpr { slexpr = SEvar alias'; _ }; _}) when alias = alias' ->
          (mk_scmd (SCdef (ty, var, se)) (loc_of_scmd sc1), cost1) :: merge_ret_def blocks'
        (* pvt int f$r0 = ...; var = f$r0; -> var = ...; *)
        | SCasgn (sle, { sexpr = SElexpr { slexpr = SEvar alias'; _}; _ }) when alias = alias' ->
          (mk_scmd (SCasgn (sle, se)) (loc_of_scmd sc1), cost1) :: merge_ret_def blocks'
        | _ -> (sc2, cost2) :: merge_ret_def ((sc1, cost1) :: blocks')
        end
      | _ -> (sc2, cost2) :: merge_ret_def ((sc1, cost1) :: blocks')
      end
    | _ -> sprog_rev
  in
  merge_ret_def sprog_rev
*)