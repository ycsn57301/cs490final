open Ast
open Builtin
open Sim

exception DereferNull of expr_node
exception FatalInSSim of string
(* these three exceptions are not runtime errors,
   but ways for us to manipulate the control flow *)
exception ReturnFromFunction of sexpr_node
exception BreakFromLoop
exception ContinueFromLoop
(* exception TODOSSim *)

(* simulation environment *************************************************** *)

type ssim_env =
  {
    (* alias related info *)
    ssim_var_count : (string, int) Hashtbl.t;
    ssim_fun_count : (string, int) Hashtbl.t;
    (* maps variable's name to its alias.
       Note: the first frame stores all global variables. *)
    ssim_alias_frames : (string, var_alias) Hashtbl.t list list ref;
    (* values' map *)
    ssim_values : svalue AliasHashtbl.t;
    (* all aliases' depths.
       The depth encodes the depth in the stack when this variable is created.
       In other words, it records when the variable is created, which is helpful in
       dealing with atomic functions.*)
    ssim_alias_depths : int AliasHashtbl.t;
    (* context *)
    ssim_fds : (string, fundef_node) Hashtbl.t; (* does not contain plocal functions *)
    ssim_fsigs : (string, funsig) Hashtbl.t;
    ssim_su_env : struct_union_env;
    ssim_atomcall_env : atomic_call_env;
    (* history of private commands with their costs *)
    ssim_history : (scmd_node * int) Queue.t;
    (* atomic related info *)
    ssim_atomic_depth : int option ref; (* None means not in atomic, Some n means atomic call starts from depth n *)
    ssim_atomic_cost : int ref;
    ssim_atomic_K0R : value LValueHashtbl.t;
    ssim_atomic_K1K2R : LValueTree.t ref;
    ssim_atomic_K1K2W : LValueTree.t ref;
  }

let string_of_frame env frame =
  "[" ^ Hashtbl.fold (fun var alias text ->
    let value_text =
      try
        let sv = AliasHashtbl.find env.ssim_values alias in
        string_of_svalue sv 
      with Not_found -> "NOT_FOUND"
    in
    var ^ " -> " ^ string_of_alias alias ^ " = " ^ value_text ^ ", " ^ text
  ) frame "" ^ "]"

let string_of_frames env frames =
  String.concat " | " (List.map (string_of_frame env) frames)

let _debug_ssim_env env =
  Logs.debug (fun m -> m "%s" (String.concat "\n" (List.map (string_of_frames env) !(env.ssim_alias_frames))))

let get_global_frame env =
  let depth = (List.length !(env.ssim_alias_frames)) in
  List.nth !(env.ssim_alias_frames) (depth-1)

let find_var_alias env var =
  let rec find_in_section_frames frames =
    match frames with
    | [] -> raise Not_found
    | frame :: frames' ->
      try Hashtbl.find frame var
      with Not_found -> find_in_section_frames frames'
  in
  let function_frame = List.hd !(env.ssim_alias_frames) in
  (* firstly search the function's local frame *)
  try find_in_section_frames function_frame
  with Not_found -> (* if not found, search the global variables frame *)
    try
      let global_frame = get_global_frame env in
      find_in_section_frames global_frame
    with Not_found -> raise (FatalInSSim ("cannot find var " ^ var))

let load_alias_svalue env alias =
  AliasHashtbl.find env.ssim_values alias

let init_alias_value env alias v =
  AliasHashtbl.add env.ssim_values alias v

let update_alias_value env alias v =
  AliasHashtbl.replace env.ssim_values alias v

let new_alias env name =
  let depth = List.length !(env.ssim_alias_frames) in
  (* create alias *)
  let alias =
    (* global variable's alias are unique *)
    if depth = 1 then AliasGlob name
    (* normal variable's alias *)
    else try
      let count = Hashtbl.find env.ssim_var_count name in
      Hashtbl.replace env.ssim_var_count name (count+1);
      AliasNorm (name, count)
    with Not_found ->
      Hashtbl.add env.ssim_var_count name 1; AliasNorm (name, 0)
  in
  (* update frame *)
  let frame = List.hd @@ List.hd !(env.ssim_alias_frames) in
  Hashtbl.add frame name alias;
  (* record depth *)
  AliasHashtbl.add env.ssim_alias_depths alias depth;
  alias

let new_var_alias = new_alias

(* let anno_name = "OU_anno" *)
(* let new_anno_alias env = new_alias true env anno_name *)

let ssim_in_atomic env =
  match !(env.ssim_atomic_depth) with
  | None -> false
  | Some _ -> true
let ssim_enter_atomic env =
  if ssim_in_atomic env then raise (FatalInSSim "enter atomic")
  else begin
    env.ssim_atomic_depth := Some (List.length !(env.ssim_alias_frames));
    env.ssim_atomic_cost := 0;
    env.ssim_atomic_K1K2W := LValueTree.empty;
    env.ssim_atomic_K1K2R := LValueTree.empty;
    LValueHashtbl.reset env.ssim_atomic_K0R
  end
let ssim_exit_atomic env =
  if ssim_in_atomic env then env.ssim_atomic_depth := None
  else raise (FatalInSSim "exit atomic");
  !(env.ssim_atomic_cost)

let ssim_add_atomic_K1K2W env lv =
  env.ssim_atomic_K1K2W := LValueTree.add lv !(env.ssim_atomic_K1K2W)
let ssim_add_atomic_K1K2R env lv =
  env.ssim_atomic_K1K2R := LValueTree.add lv !(env.ssim_atomic_K1K2R)
let ssim_add_atomic_K0R env lvmap =
  LValueMap.iter (fun lv v ->
    if not @@ LValueHashtbl.mem env.ssim_atomic_K0R lv then (* only record the first value *)
      LValueHashtbl.add env.ssim_atomic_K0R lv v
  ) lvmap

(*** Check if sle refers to an alias defined below atomic depth *)
let defined_outside_atomic env sle =
  match !(env.ssim_atomic_depth) with
  | None -> false
  | Some depth ->
    let rec is_outside base_sle =
      match base_sle.slexpr with
      | SEvar alias -> AliasHashtbl.find env.ssim_alias_depths alias < depth
      | SEindex (arr, _, _) -> is_outside arr
      | SEfield (st, _) -> is_outside st
    in
    is_outside sle

let lvalue_outside_atomic env lv =
  match !(env.ssim_atomic_depth) with
  | None -> false
  | Some depth ->
    let rec is_outside base_lv =
      match base_lv.lvalue with
      | Vvar alias -> AliasHashtbl.find env.ssim_alias_depths alias < depth
      | Vindex (lv_arr, _, _) -> is_outside lv_arr
      | Vfield (lv_st, _) -> is_outside lv_st
    in
    is_outside lv

let record_K1K2W env sle =
  if ssim_in_atomic env && defined_outside_atomic env sle then begin
    let lv_base = closest_lvalue_of_slexpr sle in
    if type_has_K1K2 env.ssim_su_env (type_of_lvalue lv_base) then
      ssim_add_atomic_K1K2W env lv_base
  end

let record_K0R env sle sv =
  if ssim_in_atomic env && defined_outside_atomic env sle then begin
    let lv_base = closest_lvalue_of_slexpr sle in
    let k0_W = indivisible_K0_lvalues env.ssim_su_env lv_base sv in
    ssim_add_atomic_K0R env k0_W
  end

let record_K1K2R env sle =
  if ssim_in_atomic env && defined_outside_atomic env sle then begin
    let lv_base = closest_lvalue_of_slexpr sle in
    if type_has_K1K2 env.ssim_su_env (type_of_lvalue lv_base) then
      ssim_add_atomic_K1K2R env lv_base
  end

let record_pointed_K1K2R env se =
  if ssim_in_atomic env then begin
    let rec record_pointed se =
      match se.sexpr with
      | SEunit | SEbool _ | SEint _ | SEfloat _ | SEnull -> ()
      | SEref lv ->
        if lvalue_outside_atomic env lv &&
           type_has_K1K2 env.ssim_su_env (type_of_lvalue lv) then
          ssim_add_atomic_K1K2R env lv
      | SElexpr _ -> () (* TODO: should we add something in this case? *)
      | SEarrayinit (_, se_inits) ->
        List.iter record_pointed se_inits
      | SEstructinit asgns ->
        List.iter (fun (_, se_field) -> record_pointed se_field) asgns
      | SEbuiltin (_, se_args) ->
        List.iter record_pointed se_args
    in
    record_pointed se
  end

(*
let rec has_unknown base_se =
  match base_se.sexpr with
  | SEunit
  | SEbool _
  | SEint _
  | SEfloat _
  | SEnull
  | SEref _ -> false
  | SElexpr _ -> true
  | SEarrayinit (Public K0Public, _) -> false
    (* List.exists (fun se -> has_unknown se) se_inits *)
  | SEarrayinit _ -> true
  | SEstructinit asgns ->
    List.exists (fun (_, se_asgn) -> has_unknown se_asgn) asgns
  (* if this builtin call can not be reduced to a value, then it must contain unknown part *)
  | SEbuiltin _ -> true
*)
let rec ty_has_unknown su_env ty =
  match ty with
  | Tunit -> false
  | Tint sec | Tfloat sec | Tbool sec ->
    if sec = Public K0Public then false
    else true
  | Tref _ -> false
  | Tarray (elem_ty, _, _) ->
    ty_has_unknown su_env elem_ty
  | Tstruct st_name ->
    let sd = find_struct su_env st_name in
    List.exists (fun (ty_field, _) ->
      ty_has_unknown su_env ty_field) sd.struct_fields

let append_to_history env sc cost =
  let perform_append () =
    (* if inside atomic function call, then accumulate cost without really
      atttaching it to the history. After atomic function call finished, the
      accumulated cost becomes the entire function call's cost. *)
    if ssim_in_atomic env then
      env.ssim_atomic_cost := cost + !(env.ssim_atomic_cost)
    (* otherwise, record the command and its cost *)
    else
      Queue.add (sc, cost) env.ssim_history
  in
  match sc.scmd with
  | SCasgn (_, se) ->
    if ty_has_unknown env.ssim_su_env (type_of_sexpr se) then
      perform_append ()
  | SCdef (_, _, se) ->
    if ty_has_unknown env.ssim_su_env (type_of_sexpr se) then
      perform_append ()
    else begin match se.sexpr with
    | SEbuiltin (f, _) ->
      if String.ends_with ~suffix:"print" f || String.ends_with ~suffix:"debug1" f then
        perform_append ()
      else ()
    | _ -> ()
    end
  | _ -> perform_append ()

(** Push a function's frame into the stack.
    A function's frame is a stack of section frames. *)
let push_function_frame env frame =
  env.ssim_alias_frames := [frame] :: !(env.ssim_alias_frames)

let pop_function_frame env =
  (* delete the frame's values *)
  let function_frame = List.hd !(env.ssim_alias_frames) in
  (* clear aliases' values to save memory space *)
  let delete_section_frame = Hashtbl.iter (fun _ alias ->
    AliasHashtbl.remove env.ssim_values alias) in
  List.iter delete_section_frame function_frame;
  (* delete the frame *)
  env.ssim_alias_frames := List.tl !(env.ssim_alias_frames)

let push_section_frame env frame =
  let function_frame = List.hd !(env.ssim_alias_frames) in
  env.ssim_alias_frames := (frame :: function_frame) :: List.tl !(env.ssim_alias_frames)

let pop_section_frame env =
  let function_frame = List.hd !(env.ssim_alias_frames) in
  let frame = List.hd @@ function_frame in
  (* delete the frame's values *)
  Hashtbl.iter (fun _ alias ->
    AliasHashtbl.remove env.ssim_values alias) frame;
  (* delete the frame *)
  env.ssim_alias_frames := (List.tl function_frame) :: (List.tl !(env.ssim_alias_frames))

let rec sstack_load env lv =
  match lv.lvalue with
  | Vvar alias ->
    load_alias_svalue env alias
  | Vindex (lv_arr, _, index) ->
    begin match sstack_load env lv_arr with
    | SVarray (_, arr) -> Array.get arr index
    | _ -> raise (FatalInSSim "sstack_load: index")
    end
  | Vfield (lv_st, field) ->
    begin match sstack_load env lv_st with
    | SVstruct st -> Hashtbl.find st field
    | _ -> raise (FatalInSSim "sstack_load: field")
    end

let sstack_store env lv sv =
  match lv.lvalue with
  | Vvar alias ->
    update_alias_value env alias sv
  | Vindex (lv_arr, _, index) ->
    begin match sstack_load env lv_arr with
    | SVarray (_, sarr) ->
      Array.set sarr index sv
    | _ -> raise (FatalInSSim "sstack_store: index")
    end
  | Vfield (lv_st, field) ->
    begin match sstack_load env lv_st with
    | SVstruct stbl -> Hashtbl.replace stbl field sv
    | _ -> raise (FatalInSSim "sstack_store: field")
    end

(** Compute the cost of evaluating an expression's zk-circuit *)
let rec cost_expr base_se =
  match base_se.sexpr with
  | SEunit
  | SEbool _
  | SEint _
  | SEfloat _
  | SEnull
  | SEref _ -> 0
  | SElexpr sle -> cost_lexpr sle
  | SEarrayinit (_, se_inits) ->
    List.fold_left (fun acc se_init -> acc + cost_expr se_init) 0 se_inits
  | SEstructinit se_asgns ->
    List.fold_left (fun acc (_, se_asgn) -> acc + cost_expr se_asgn) 0 se_asgns
  | SEbuiltin (f, se_args) ->
    let f_cost = Hashtbl.find builtin_costs f in
    List.fold_left (fun acc se_arg -> acc + cost_expr se_arg) f_cost se_args
  and cost_lexpr base_sle =
  match base_sle.slexpr with
  | SEvar _ -> 0
  | SEindex (sle_base, Private _, se_index) ->
    let pvt_access_cost = 10000 in (* FIXME: accurate cost *)
    cost_lexpr sle_base + cost_expr se_index + pvt_access_cost
  | SEindex (sle_base, _, _) ->
    cost_lexpr sle_base
  | SEfield (sle_base, _) -> cost_lexpr sle_base

let rec cost_slexpr base_sle =
  match base_sle.slexpr with
  | SEvar _ -> 0
  | SEindex (sle_arr, _, se_index) -> cost_slexpr sle_arr + cost_expr se_index
  | SEfield (sle_st, _) -> cost_slexpr sle_st

(* shallow simulation ******************************************************* *)

let rec ssim_expr env e =
  let ret raw_se = mk_sexpr raw_se (type_of_expr e) (loc_of_expr e) in
  match e.expr with
  | Eunit -> ret SEunit
  | Ebool b -> ret (SEbool b)
  | Eint n -> ret (SEint n)
  | Efloat f -> ret (SEfloat f)
  | Enull -> ret SEnull
  | Elexpr le ->
    let sle = ssim_lexpr env le in
    ssim_load env sle
  | Eref le -> (* all pointers have to be K0, so we can safely convert lexpr to lvalue *)
    let sle = ssim_lexpr env le in
    let lv = match lvalue_of_slexpr sle with
    | Some lv -> lv
    | _ -> raise (FatalInSSim "ssim_expr: Eref")
    in
    ret (SEref lv)
  | Earrayinit (sec, e_inits) ->
    let se_inits = List.map (ssim_expr env) e_inits in
    ret (SEarrayinit (sec, se_inits))
  | Estructinit e_asgns ->
    let se_asgns = List.map (fun (field, e) -> (field, ssim_expr env e)) e_asgns in
    ret (SEstructinit se_asgns)
  | Ebuiltin (f, args) ->
    (* evaluate builtin directly *)
    let builtin_f = Builtin.ssim_builtin f in
    let se_args = List.map (ssim_expr env) args in
    ret (builtin_f se_args)

(* Evaluate the index of array access, and replace deref with lexpr. *)
and ssim_lexpr env le =
  let raw_sle = match le.lexpr with
  | Evar (name, _) ->
    let alias = find_var_alias env name in
    SEvar alias
  | Ederef e ->
    let se = ssim_expr env e in
    begin match se.sexpr with
    | SEnull -> raise (DereferNull e)
    | SEref lv -> (slexpr_of_lvalue lv).slexpr
    | _ -> raise (FatalInSSim "ssim_lexpr: deref")
    end
  | Eindex (le_arr, sec, e_index) ->
    let sle_arr = ssim_lexpr env le_arr in
    let se_index = ssim_expr env e_index in
    SEindex (sle_arr, sec, se_index)
  | Efield (le_st, field) ->
    let sle_st = ssim_lexpr env le_st in
    SEfield (sle_st, field)
  in
  mk_slexpr raw_sle (type_of_lexpr le) (loc_of_lexpr le)

(** Load the data from location sle. *)
and ssim_load env sle =
  match lvalue_of_slexpr sle with
  | Some lv -> (* K0 lvalue, try load *)
    let sv = sstack_load env lv in
    record_K1K2R env sle;
    record_K0R env sle sv;
    sexpr_of_svalue sv lv
  | None -> (* K1/K2 lvalue, can not load *)
    record_K1K2R env sle;
    mk_sexpr (SElexpr sle) (type_of_slexpr sle) (loc_of_slexpr sle)

(** Store [se_data] into the location pointed by sle.
    Turn [se_data] into svalue, store it into a location, then update the history. *)
and ssim_store env sle se_data =
  (* update stack *)
  begin match lvalue_of_slexpr sle with
  | Some lv ->
    let sv = svalue_of_sexpr false env.ssim_su_env se_data in
    sstack_store env lv sv
  | None -> ()
  end;
  (* update history *)
  let raw_sc = SCasgn (sle, se_data) in
  let sc = mk_scmd raw_sc (loc_of_slexpr sle) in
  let cost = cost_slexpr sle + cost_expr se_data in
  append_to_history env sc cost;
  record_K1K2W env sle

and ssim_cmd env c =
  match c.cmd with
  | Cskip -> ()
  | Cseq (c1, c2) -> ssim_cmd env c1; ssim_cmd env c2
  | Cdef (ty, var, e_init) ->
    let se_init = ssim_expr env e_init in
    ssim_vardef env ty var se_init (loc_of_cmd c)
  | Ccall (var_ty, anno, var, f, args) ->
    let se_args = List.map (ssim_expr env) args in
    begin match anno with
    | NORMAL | ATOMIC ->
      ssim_call env var f se_args (loc_of_cmd c)
    | SANDBOX a ->
      let alias = new_var_alias env var in
      (* store an uninitialized svalue into the stack *)
      let sv_ret = uninit_svalue_of_typ false env.ssim_su_env var_ty in
      init_alias_value env alias sv_ret;
      (* record pointers appearing in the arguments *)
      List.iter (record_pointed_K1K2R env) se_args;
      (* add call command to history *)
      let raw_sc = SCsandboxcall (var_ty, a, alias, f, se_args) in
      let sc = mk_scmd raw_sc (loc_of_cmd c) in
      let cost = List.fold_left (fun acc se_arg -> acc + cost_expr se_arg) 0 se_args in
      append_to_history env sc cost
    end
  | Casgn (le, e) ->
    let sle = ssim_lexpr env le in
    let se = ssim_expr env e in
    ssim_store env sle se
  | Cif (e, c1, c2) ->
    let se = ssim_expr env e in
    let cond = begin match se.sexpr with
    | SEbool b -> b
    | _ -> raise (FatalInSSim "ssim_cmd: Cif")
    end in
    if cond then
      ssim_cmd env c1
    else
      ssim_cmd env c2
  | Cwhile (e, c1) ->
    (* basic_loop does not handle break nor continue *)
    let rec basic_loop _ =
      let se = ssim_expr env e in
      let cond = begin match se.sexpr with
      | SEbool b -> b
      | _ -> raise (FatalInSSim "ssim_cmd: Cwhile")
      end in
      (* execute loop body then iterate *)
      if cond then
        begin ssim_cmd env c1; basic_loop () end
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
    ssim_cmd env c1;
    pop_section_frame env
  | Creturn e ->
    let se = ssim_expr env e in
    raise (ReturnFromFunction se)
  | Cbreak -> raise BreakFromLoop
  | Ccontinue -> raise ContinueFromLoop
  | Cassert e ->
    let se = ssim_expr env e in
    match se.sexpr with
    | SEbool true -> ()
    | SEbool false -> raise (FatalInSSim ("assertion failed: " ^ string_of_expr_node e))
    | _ -> (* append to history *)
      let raw_sc = SCassert se in
      let sc = mk_scmd raw_sc (loc_of_cmd c) in
      let cost = cost_expr se in
      append_to_history env sc cost


and ssim_call env var f se_args loc =
  let fd_node = Hashtbl.find env.ssim_fds f in
  let fd = fd_node.fundef in
  let ret_typ = fd.fun_ret_typ in
  let f_alias = new_var_alias env var in
  (* create new frame *)
  push_function_frame env (Hashtbl.create 20);
  let compute_ret _ =
    try
      ssim_cmd env fd.fun_body;
      raise (FatalInSSim "ssim_call: no return")
    with ReturnFromFunction se -> se
  in
  (* If this is an atomic invocation, then f_alias is bound to SCcall;
     Otherwise, f_alias is bound to the private part of the returned value. *)
  let se_ret =
  if fd.fun_anno = ATOMIC && not (ssim_in_atomic env) then begin
    (* bind arguments *)
    List.iter2 (fun (typ, var) se_arg ->
      ssim_vardef ~skip_update_history:true env typ var se_arg (loc_of_sexpr se_arg)
      ) fd.fun_params se_args;
    ssim_enter_atomic env; (* assume arguments are simplified before entering atomic environment *)
    let se_ret = compute_ret () in
    (* the cost is accumulated *)
    let ret_cost = cost_expr se_ret in
    let fun_cost = ssim_exit_atomic env in
    let cost = fun_cost + ret_cost in
    (* record atomcall's info *)
    let k0R = List.of_seq @@ LValueHashtbl.to_seq env.ssim_atomic_K0R in
    let info = {
      liveinfo_K1K2_R = !(env.ssim_atomic_K1K2R);
      liveinfo_K1K2_W = !(env.ssim_atomic_K1K2W);
    } in
    atomcall_record env.ssim_atomcall_env f_alias info;
    (* update history *)
    let raw_sc = SCcall (ret_typ, f_alias, f, se_args, k0R) in
    let sc = mk_scmd raw_sc loc in
    append_to_history env sc cost;
    se_ret
  end
  (* already in atomic or outside atomic *)
  else begin
    (* bind arguments *)
    List.iter2 (fun (ty, var) se_arg ->
      ssim_vardef env ty var se_arg (loc_of_sexpr se_arg)
      ) fd.fun_params se_args;
    let se_ret = compute_ret () in
    (* append to history *)
    let raw_sc = SCdef (fd.fun_ret_typ, f_alias, se_ret) in
    let sc = mk_scmd raw_sc loc in
    let cost = cost_expr se_ret in
    append_to_history env sc cost;
    se_ret
  end
  in
  (* pop frame *)
  pop_function_frame env;
  (* store receiver's value into env *)
  init_alias_value env f_alias (svalue_of_sexpr false env.ssim_su_env se_ret)

(** `skip_update_history` is useful when evaluating arguments. *)
and ssim_vardef ?(skip_update_history = false) env ty var se_init loc =
  (* create alias *)
  let alias = new_var_alias env var in
  (* record value *)
  let sv = svalue_of_sexpr false env.ssim_su_env se_init in
  init_alias_value env alias sv;
  (* only update history when [se_init] has K1/K2 info. Also skip global variables *)
  if not (is_global_alias alias) && not skip_update_history then begin
    (* update history *)
    let raw_sc = SCdef (ty, alias, se_init) in
    let sc = mk_scmd raw_sc loc in
    let cost = cost_expr se_init in
    append_to_history env sc cost
  end

let ssim_gvardef env gd_node =
  let gd = gd_node.gvardef in
  let se_init = ssim_expr env gd.gvar_init in
  let _ = ssim_vardef env gd.gvar_typ gd.gvar_name se_init (loc_of_gvardef gd_node) in ()

let ssim_prog gvar_defs fun_defs fun_sigs su_env =
  let env = {
    ssim_var_count = Hashtbl.create 40;
    ssim_fun_count = Hashtbl.create (List.length fun_defs);
    ssim_fds = Hashtbl.create (List.length fun_defs);
    ssim_fsigs = fun_sigs;
    ssim_su_env = su_env;
    ssim_atomcall_env = AliasHashtbl.create 40;
    ssim_alias_frames = ref [[Hashtbl.create (List.length gvar_defs)]];
    ssim_alias_depths = AliasHashtbl.create 40;
    ssim_values = AliasHashtbl.create 40;
    ssim_history = Queue.create ();
    ssim_atomic_depth = ref None;
    ssim_atomic_cost = ref 0;
    ssim_atomic_K0R = LValueHashtbl.create 40;
    ssim_atomic_K1K2R = ref LValueTree.empty;
    ssim_atomic_K1K2W = ref LValueTree.empty; }
  in
  (* record functions *)
  List.iter (fun fd_node ->
    let fd = fd_node.fundef in
    Hashtbl.add env.ssim_fds fd.fun_name fd_node) fun_defs;
  (* initialize global variables *)
  List.iter (ssim_gvardef env) gvar_defs;
  (* start executing main function. There's no explict invocation of the main
     function, so we set its location as none. *)
  ssim_call env "OU_main_r" "main" [] Location.none;
  Array.of_seq (Queue.to_seq env.ssim_history), env.ssim_atomcall_env
