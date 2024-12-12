open Ast
open Sim
open Analysis
(* open Util *)

(* exception TODOdsim *)
(* exception UninterpretedBuiltin of string * value list *)
exception FatalInDSim of string
exception DereferNull of expr_node
exception BreakFromLoop
exception ContinueFromLoop
exception ReturnFromFunction of sexpr_node

(* deep-simulation environment ********************************************** *)

type dsim_env =
{
  (* Note: all aliases counts in deep-sim are negative, so that we can avoid
     conflict with aliases generated in shallow-sim. *)
  dsim_var_count : (string, int) Hashtbl.t;
  dsim_fun_count : (string, int) Hashtbl.t;
  dsim_alias_frames : (string, var_alias) Hashtbl.t list list ref;
  dsim_values : svalue AliasHashtbl.t;
  dsim_su_env : struct_union_env;
  dsim_funs : (string, fundef_node) Hashtbl.t;
}

let string_of_frame env frame =
  "[" ^ Hashtbl.fold (fun var alias text ->
    let value_text =
      try
        let sv = AliasHashtbl.find env.dsim_values alias in
        string_of_svalue sv 
      with Not_found -> "NOT_FOUND"
    in
    var ^ " -> " ^ string_of_alias alias ^ " = " ^ value_text ^ ", " ^ text
  ) frame "" ^ "]"

let string_of_frames env frames =
  String.concat " | " (List.map (string_of_frame env) frames)

let _debug_dsim_env env =
  Logs.debug (fun m -> m "%s" (String.concat "\n" (List.map (string_of_frames env) !(env.dsim_alias_frames))))

let get_global_frame env =
  let depth = (List.length !(env.dsim_alias_frames)) in
  List.nth !(env.dsim_alias_frames) (depth-1)

let find_var_alias env var =
  let rec find_in_section_frames frames =
    match frames with
    | [] -> raise Not_found
    | frame :: frames' ->
      try Hashtbl.find frame var
      with Not_found -> find_in_section_frames frames'
  in
  let function_frame = List.hd !(env.dsim_alias_frames) in
  (* firstly search the function's local frame *)
  try find_in_section_frames function_frame
  with Not_found -> (* if not found, search the global variables frame *)
    try
      let global_frame = get_global_frame env in
      find_in_section_frames global_frame
    with Not_found -> begin
      _debug_dsim_env env;
      raise (FatalInDSim ("cannot find var " ^ var))
    end

(** Push a function's frame into the stack.
    A function's frame is a stack of section frames. *)
let push_function_frame env frame =
  env.dsim_alias_frames := [frame] :: !(env.dsim_alias_frames)

let pop_function_frame env =
  (* delete the frame's values *)
  let function_frame = List.hd !(env.dsim_alias_frames) in
  (* clear aliases' values to save memory space *)
  let delete_section_frame = Hashtbl.iter (fun _ alias ->
    AliasHashtbl.remove env.dsim_values alias) in
  List.iter delete_section_frame function_frame;
  (* delete the frame *)
  env.dsim_alias_frames := List.tl !(env.dsim_alias_frames)

let push_section_frame env frame =
  let function_frame = List.hd !(env.dsim_alias_frames) in
  env.dsim_alias_frames := (frame :: function_frame) :: List.tl !(env.dsim_alias_frames)

let pop_section_frame env =
  let function_frame = List.hd !(env.dsim_alias_frames) in
  let frame = List.hd @@ function_frame in
  (* delete the frame's values *)
  Hashtbl.iter (fun _ alias ->
    AliasHashtbl.remove env.dsim_values alias) frame;
  (* delete the frame *)
  env.dsim_alias_frames := (List.tl function_frame) :: (List.tl !(env.dsim_alias_frames))

let load_alias_value env alias =
  AliasHashtbl.find env.dsim_values alias

let init_alias_value env alias v =
  AliasHashtbl.add env.dsim_values alias v

let update_alias_value env alias v =
  AliasHashtbl.replace env.dsim_values alias v

let add_alias_to_frame env alias =
  let name = match alias with
    | AliasNorm (name, _) -> name
    | AliasGlob name -> name
  in
  let frame = List.hd @@ List.hd !(env.dsim_alias_frames) in
  Hashtbl.add frame name alias

let new_alias env name =
  let depth = List.length !(env.dsim_alias_frames) in
  (* create alias *)
  let alias =
    (* global variable's alias are unique *)
    if depth = 1 then AliasGlob name
    (* normal variable's alias *)
    else try
      let count = Hashtbl.find env.dsim_var_count name in
      Hashtbl.replace env.dsim_var_count name (count-1);
      AliasNorm (name, count)
    with Not_found ->
      Hashtbl.add env.dsim_var_count name (-2); AliasNorm (name, -1)
  in
  (* update frame *)
  add_alias_to_frame env alias;
  alias

let new_var_alias = new_alias
(* let new_fun_alias = new_alias false *)

let rec dstack_load env lv =
  match lv.lvalue with
  | Vvar alias ->
    load_alias_value env alias
  | Vindex (lv_arr, _, index) ->
    begin match dstack_load env lv_arr with
    | SVarray (_, arr) -> Array.get arr index
    | _ -> raise (FatalInDSim "sstack_load: index")
    end
  | Vfield (lv_st, field) ->
    begin match dstack_load env lv_st with
    | SVstruct st -> Hashtbl.find st field
    | _ -> raise (FatalInDSim "sstack_load: field")
    end

let dstack_store env lv sv =
  match lv.lvalue with
  | Vvar alias ->
    update_alias_value env alias sv
  | Vindex (lv_arr, _, index) ->
    begin match dstack_load env lv_arr with
    | SVarray (_, sarr) -> Array.set sarr index sv
    | _ -> raise (FatalInDSim "sstack_store: index")
    end
  | Vfield (lv_st, field) ->
    begin match dstack_load env lv_st with
    | SVstruct stbl -> Hashtbl.replace stbl field sv
    | _ -> raise (FatalInDSim "sstack_store: field")
    end

(* deep-simulate commands *************************************************** *)

let rec dsim_expr env e =
  let ret raw_se = mk_sexpr raw_se (type_of_expr e) (loc_of_expr e) in
  match e.expr with
  | Eunit -> ret SEunit
  | Ebool b -> ret (SEbool b)
  | Eint n -> ret (SEint n)
  | Efloat f -> ret (SEfloat f)
  | Enull -> ret SEnull
  | Elexpr le ->
    let sle = dsim_lexpr env le in
    dsim_load env sle
  | Eref le ->
    let sle = dsim_lexpr env le in
    let lv = match lvalue_of_slexpr sle with
    | Some lv -> lv
    | _ -> raise (FatalInDSim "dsim_expr: Eref")
    in
    ret (SEref lv)
  | Earrayinit (sec, e_inits) ->
    let se_inits = List.map (dsim_expr env) e_inits in
    ret (SEarrayinit (sec, se_inits))
  | Estructinit e_asgns ->
    let se_asgns = List.map (fun (field, e) -> (field, dsim_expr env e)) e_asgns in
    ret (SEstructinit se_asgns)
  | Ebuiltin (f_name, e_args) ->
    (* evaluate builtin directly *)
    let builtin_f = Builtin.dsim_builtin f_name in
    let se_args = List.map (dsim_expr env) e_args in
    ret (builtin_f se_args)

and dsim_lexpr env le =
  let raw_sle = match le.lexpr with
  | Evar (name, _) ->
    let alias = find_var_alias env name in
    SEvar alias
  | Ederef e ->
    let se = dsim_expr env e in
    begin match se.sexpr with
    | SEnull -> raise (DereferNull e)
    | SEref lv -> (slexpr_of_lvalue lv).slexpr
    | _ -> raise (FatalInDSim "dsim_lexpr: deref")
    end
  | Eindex (le_arr, sec, e_index) ->
    let sle_arr = dsim_lexpr env le_arr in
    let se_index = dsim_expr env e_index in
    SEindex (sle_arr, sec, se_index)
  | Efield (le_st, field) ->
    let sle_st = dsim_lexpr env le_st in
    SEfield (sle_st, field)
  in
  mk_slexpr raw_sle (type_of_lexpr le) (loc_of_lexpr le)

and dsim_load env sle =
  match lvalue_of_slexpr sle with
  | Some lv ->
    let sv = dstack_load env lv in
    sexpr_of_svalue sv lv
  | None ->
    mk_sexpr (SElexpr sle) (type_of_slexpr sle) (loc_of_slexpr sle)

and dsim_store env sle se_data =
  (* update stack *)
  begin match lvalue_of_slexpr sle with
  | Some lv ->
    let sv = svalue_of_sexpr true env.dsim_su_env se_data in
    dstack_store env lv sv
  | None -> ()
  end

and dsim_vardef env var se_init =
  (* create alias *)
  let alias = new_var_alias env var in
  (* record value *)
  init_alias_value env alias (svalue_of_sexpr true env.dsim_su_env se_init)

and dsim_cmd env c =
  match c.cmd with
  | Cskip -> ()
  | Cseq (c1, c2) -> dsim_cmd env c1; dsim_cmd env c2
  | Cdef (_, var, init) ->
    let se_init = dsim_expr env init in
    dsim_vardef env var se_init
  | Ccall (ret_ty, anno, var_name, f_name, e_args) ->
    begin match anno with
    | NORMAL | ATOMIC | SANDBOX PLOCAL1 | SANDBOX BLACKBOX1 ->
      let se_args = List.map (dsim_expr env) e_args in
      dsim_call env var_name f_name se_args
    | _ -> (* ignore BLACKBOX2 and PLOCAL2 *)
      let sv_ret = uninit_svalue_of_typ true env.dsim_su_env ret_ty in
      let alias = new_var_alias env var_name in
      init_alias_value env alias sv_ret
    end
  | Casgn (le, e) ->
    let sle = dsim_lexpr env le in
    let se = dsim_expr env e in
    dsim_store env sle se
  | Cif (e, c1, c2) ->
    let se = dsim_expr env e in
    let cond = begin match se.sexpr with
    | SEbool b -> b
    | _ -> raise (FatalInDSim "dsim_cmd: Cif")
    end in
    if cond then
      dsim_cmd env c1
    else
      dsim_cmd env c2
  | Cwhile (e, c1) ->
    (* basic_loop does not handle break nor continue *)
    let rec basic_loop _ =
      let se = dsim_expr env e in
      let cond = begin match se.sexpr with
      | SEbool b -> b
      | _ -> raise (FatalInDSim "dsim_cmd: Cwhile")
      end in
      (* execute loop body then iterate *)
      if cond then
        begin dsim_cmd env c1; basic_loop () end
    (* continuable_loop can be terminated by break, while continue causes it to iterate. *)
    and continuable_loop _ =
      try
        basic_loop ()
      with
      | BreakFromLoop -> ()
      | ContinueFromLoop -> continuable_loop ()
    in
    continuable_loop ()
  | Csection c1 ->
    push_section_frame env (Hashtbl.create 20);
    dsim_cmd env c1;
    pop_section_frame env
  | Creturn e ->
    let se = dsim_expr env e in
    raise (ReturnFromFunction se)
  | Cbreak -> raise BreakFromLoop
  | Ccontinue -> raise ContinueFromLoop
  | Cassert e ->
    let se = dsim_expr env e in
    match se.sexpr with
    | SEbool true -> ()
    | SEbool false -> raise (FatalInDSim ("assertion failed: " ^ string_of_expr_node e))
    | _ -> () (* decide during runtime *)

and dsim_call env var_name f_name se_args =
  let fd_node = Hashtbl.find env.dsim_funs f_name in
  let fd = fd_node.fundef in
  (* create new frame *)
  push_function_frame env (Hashtbl.create 20);
  (* bind arguments *)
  List.iter2 (fun (_, var) se_arg ->
    dsim_vardef env var se_arg) fd.fun_params se_args;
  (* compute function body *)
  let se_ret = try
    dsim_cmd env fd.fun_body;
    raise (FatalInDSim "sim_call: no return")
  with ReturnFromFunction v -> v
  in
  (* pop frame *)
  pop_function_frame env;
  (* store return value *)
  let alias = new_var_alias env var_name in
  init_alias_value env alias (svalue_of_sexpr true env.dsim_su_env se_ret)

(* deep-simulate symbolic commands ****************************************** *)

(** Evaluate a K1K2 sexpr with K1 knowledge *)
let rec dsim_sexpr env se =
  let ret raw_se = mk_sexpr raw_se (type_of_sexpr se) (loc_of_sexpr se) in
  match se.sexpr with
  | SEunit
  | SEbool _
  | SEint _
  | SEfloat _
  | SEnull
  | SEref _ -> se
  | SElexpr sle ->
    let sle' = dsim_slexpr env sle in
    dsim_load env sle'
    (*
    let sv_result = dsim_load env sle' in
    let opt_result = value_of_K0K1_svalue sv_result in
    (* simplify the result if [sle] points to K0/K1 *)
      begin match opt_result with
    | Some v -> ret (SEvalue v)
    | None -> ret (SElexpr sle')
    end
    *)
  | SEarrayinit (sec, se_inits) ->
    let se_inits' = List.map (dsim_sexpr env) se_inits in
    ret (SEarrayinit (sec, se_inits'))
  | SEstructinit se_asgns ->
    let se_asgns' = List.map (fun (field, e) -> (field, dsim_sexpr env e)) se_asgns in
    ret (SEstructinit se_asgns')
  | SEbuiltin (f, se_args) ->
    let builtin_f = Builtin.dsim_builtin f in
    let se_args' = List.map (dsim_sexpr env) se_args in
    let se_res = builtin_f se_args' in
    ret se_res

and dsim_slexpr env sle =
  let raw_sle = match sle.slexpr with
  | SEvar alias -> SEvar alias
  | SEindex (sle_arr, sec, se_index) ->
    let sle_arr' = dsim_slexpr env sle_arr in
    let se_index' = dsim_sexpr env se_index in
    SEindex (sle_arr', sec, se_index')
  | SEfield (sle_st, field) ->
    let sle_st' = dsim_slexpr env sle_st in
    SEfield (sle_st', field)
  in
  mk_slexpr raw_sle (type_of_slexpr sle) (loc_of_slexpr sle)

and dsim_scall env f_name se_args =
  let fd_node = Hashtbl.find env.dsim_funs f_name in
  let fd = fd_node.fundef in
  (* create new frame *)
  push_function_frame env (Hashtbl.create 20);
  (* bind argument, no need to memorize these parameters *)
  List.iter2 (fun (_, var) se_arg ->
    dsim_vardef env var se_arg) fd.fun_params se_args;
  (* compute function body *)
  let se_ret = try
    dsim_cmd env fd.fun_body;
    raise (FatalInDSim "sim_call: no return")
  with ReturnFromFunction v -> v
  in
  pop_function_frame env;
  se_ret

let dsim_scmd env sc =
  match sc.scmd with
  | SCdef (_, alias, se_init) ->
    let se_init' = dsim_sexpr env se_init in
    add_alias_to_frame env alias;
    init_alias_value env alias (svalue_of_sexpr true env.dsim_su_env se_init')
  | SCasgn (sle, se) ->
    let sle' = dsim_slexpr env sle in
    let se' = dsim_sexpr env se in
    dsim_store env sle' se'
  | SCassert se ->
    begin match (dsim_sexpr env se).sexpr with
    | SEbool true -> ()
    | SEbool false -> raise (FatalInDSim ("assertion failed: " ^ string_of_sexpr_node se))
    | _ -> () (* must contain K2 info, so we defer it to runtime *)
    end
  | SCcall (_, f_alias, f_name, se_args, pubR) ->
    (* bind pubR *)
    List.iter (fun (lv, v) ->
      let ty, alias = base_of_lvalue lv in
      (* if the alias does not exist in the context, then create one without initializing *)
      if not (AliasHashtbl.mem env.dsim_values alias) then begin
        let sv_base = uninit_svalue_of_typ true env.dsim_su_env ty in
        init_alias_value env alias sv_base
      end;
      (* update this public value *)
      let sv = svalue_of_value env.dsim_su_env (type_of_lvalue lv) v in
      dstack_store env lv sv) pubR;
    (* add global variables into stack so later in the body, these variables can be assigned *)
    let glob_frame = List.hd (get_global_frame env) in
    List.iter (fun (lv, _) ->
      let _, alias = base_of_lvalue lv in
      match alias with
      | AliasGlob name when not (Hashtbl.mem glob_frame name) ->
        Hashtbl.add glob_frame name alias
      | _ -> ()) pubR;
    (* eval arguments *)
    let se_args' = List.map (dsim_sexpr env) se_args in
    (* run function call *)
    let se_ret = dsim_scall env f_name se_args' in
    let sv_ret = svalue_of_sexpr true env.dsim_su_env se_ret in
    (* TODO: delete pubR? *)
    (* bind return value with alias *)
    init_alias_value env f_alias sv_ret
  | SCsandboxcall (ret_ty, a, f_alias, f_name, se_args) ->
    let se_args' = List.map (dsim_sexpr env) se_args in
    match a with
    | BLACKBOX1 | PLOCAL1 ->
      let se_ret = dsim_scall env f_name se_args' in
      let sv_ret = svalue_of_sexpr true env.dsim_su_env se_ret in
      init_alias_value env f_alias sv_ret
    | BLACKBOX2 | PLOCAL2 ->
      let sv_ret = uninit_svalue_of_typ true env.dsim_su_env ret_ty in
      init_alias_value env f_alias sv_ret
(*
let rec expr_of_typed_lvalue lv =
  let raw_e = match lv.lvalue with
  | Vvar alias -> Evar (name_of_alias alias, is_global_alias alias)
  | Vindex (lv, sec, index) ->
    let e_index = mk_expr (Eint index) (Tint sec) Location.none in
    Eindex (expr_of_typed_lvalue lv, sec, e_index)
  | Vfield (lv, field) -> Efield (expr_of_typed_lvalue lv, field)
  in mk_lexpr raw_e (type_of_lvalue lv) Location.none

(** TODO: this function is very ad-hoc.
    It is only used to convert a value to an expression so that latter empgen can print it out properly.
    So it is fine to be this ad-hoc, as we really do not care about klvl in the generated code.
    But in the long run, we should add typing information to value and generate emp code directly from the value. *)
let rec expr_of_typed_indivisible_value ty v =
  let raw_e = match ty, v with
  | Tunit, Vunit -> Eunit
  | Tbool (Public _), Vbool b -> Ebool b
  | Tbool (Plocal _), Vbool b -> Ebuiltin ("k1plc_bool_of_pub", [mk_expr (Ebool b) (Tbool (Public K0Public)) Location.none])
  | Tbool (Private _), Vbool b -> Ebuiltin ("k1pvt_bool_of_pub", [mk_expr (Ebool b) (Tbool (Public K0Public)) Location.none])
  | Tint (Public _), Vint i -> Eint i
  | Tint (Plocal _), Vint i -> Ebuiltin ("k1plc_int_of_pub", [mk_expr (Eint i) (Tint (Public K0Public)) Location.none])
  | Tint (Private _), Vint i -> Ebuiltin ("k1pvt_int_of_pub", [mk_expr (Eint i) (Tint (Public K0Public)) Location.none])
  | Tfloat (Public _), Vfloat f -> Efloat f
  | Tfloat (Plocal _), Vfloat f -> Ebuiltin ("k1plc_float_of_pub", [mk_expr (Efloat f) (Tfloat (Public K0Public)) Location.none])
  | Tfloat (Private _), Vfloat f -> Ebuiltin ("k1pvt_float_of_pub", [mk_expr (Efloat f) (Tfloat (Public K0Public)) Location.none])
  | Tref _, Vref lv -> Eref (expr_of_typed_lvalue lv)
  | Tarray (elem_ty, sec, _), Varray arr ->
    Earrayinit (sec, List.map (expr_of_typed_indivisible_value elem_ty) (Array.to_list arr))
  | Tstruct _, _ -> raise (FatalInDSim "struct is divisible")
  | _, _ -> raise (FatalInDSim ("unmatched type " ^ string_of_typ ty ^ " and indivisible value " ^ string_of_value v))
  in
  mk_expr raw_e ty Location.none
*)
let rec merge_type_value su_env ty v =
  match ty, v with
  | Tunit, Vunit -> TVunit
  | Tint sec, Vint i -> TVint (sec, i)
  | Tfloat sec, Vfloat f -> TVfloat (sec, f)
  | Tbool sec, Vbool b -> TVbool (sec, b)
  | Tref _, Vref lv -> TVref lv
  | Tref _, Vnull -> TVnull
  | Tarray (ty_elem, sec, size), Varray arr ->
    let tv_arr = Array.map (fun v -> merge_type_value su_env ty_elem v) arr in
    TVarray (ty_elem, sec, size, tv_arr)
  | Tstruct _, Vstruct tbl ->
    let map = StringMap.of_seq (Seq.map (fun (field, v) ->
      let ty_field = get_field_type su_env field in
      (field, merge_type_value su_env ty_field v)) (Hashtbl.to_seq tbl)) in
    TVstruct map
  | _, _ -> raise (FatalInDSim ("unmatched type " ^ string_of_typ ty ^ "and value " ^ string_of_value v))
(*
let eval_edge_vars fds gvars su_env chunks =
  let env = {
    dsim_var_count = Hashtbl.create 40;
    dsim_fun_count = Hashtbl.create 40;
    dsim_alias_frames = ref [[Hashtbl.create 40]];
    dsim_values = AliasHashtbl.create 40;
    dsim_su_env = su_env;
    dsim_funs = Hashtbl.of_seq (List.to_seq (List.map (fun fd -> fd.fundef.fun_name, fd) fds)) }
  in
  (* add global variables into env *)
  List.iter (fun gvar_node ->
    let gvar = gvar_node.gvardef in
    let se_init = dsim_expr env gvar.gvar_init in
    dsim_vardef env gvar.gvar_name se_init) gvars;
  (* compute init commands *)
  dsim_call env "OU_init_r" "init" [];
  let eval_lv lv =
    let ty = type_of_lvalue lv in
    let sv = dstack_load env lv in
    let v = match value_of_K0K1_svalue sv with
    | Some v -> v
    | None ->
      raise (FatalInDSim "live-in is not K0K1")
    in
    (* we need the typing info about the v, otherwise, a private variable might be assigned with a public value in the generated code *)
    lv, expr_of_typed_indivisible_value ty v
  in
  List.map (fun chunk ->
    (* eval live-in *)
    let pvt_in = List.map eval_lv chunk.chunk_pvt_in in
    (* run program *)
    List.iter (dsim_scmd env) chunk.chunk_prog;
    pvt_in) chunks
*)
let dsim_prog fds su_env sprog depnodes =
  let env = {
    dsim_var_count = Hashtbl.create 40;
    dsim_fun_count = Hashtbl.create 40;
    dsim_alias_frames = ref [[Hashtbl.create 40]];
    dsim_values = AliasHashtbl.create 40;
    dsim_su_env = su_env;
    dsim_funs = Hashtbl.of_seq (List.to_seq (List.map (fun fd -> fd.fundef.fun_name, fd) fds)) }
  in
  let eval_lv lv =
    let ty = type_of_lvalue lv in
    let sv = dstack_load env lv in
    let v = match value_of_K0K1_svalue sv with
    | Some v -> v
    | None ->
      raise (FatalInDSim "live-in is not K0K1")
    in
    (* we need the typing info about the v, otherwise, a private variable might be assigned with a public value in the generated code *)
    merge_type_value su_env ty v
  in
  let size = Array.length sprog in
  let deps = Array.init size (fun _ -> LValueHashtbl.create 0) in
  let record_deps cmd_id depnode =
    List.iter (fun (_, _, lvs) ->
      List.iter (fun lv ->
        let e = eval_lv lv in
        LValueHashtbl.add (deps.(cmd_id)) lv e
      ) lvs
    ) depnode.depnode_deps
  in
  Array.iteri (fun cmd_id sc ->
    (* comupte dependent lvalues *)
    record_deps cmd_id depnodes.(cmd_id);
    (* run command *)
    dsim_scmd env sc
  ) sprog;
  deps
