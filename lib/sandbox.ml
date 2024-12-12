open Ast

exception SandboxUseGlobal of string * fun_anno_kind
(* exception SandboxParamPointer of string * fun_anno_kind *)
(* exception TODO *)

let rec expr_no_global e =
  match e.expr with
  | Eunit | Ebool _ | Eint _ | Efloat _ | Enull -> true
  | Elexpr le
  | Eref le -> lexpr_no_global le
  | Ebuiltin (_, args) -> List.for_all expr_no_global args
  | Earrayinit (_, inits) -> List.for_all expr_no_global inits
  | Estructinit asgns -> List.for_all (fun (_, e) -> expr_no_global e) asgns
and lexpr_no_global le =
  match le.lexpr with
  | Evar (_, is_global) -> not is_global (* the only interesting case *)
  | Eindex (le, _, e) -> lexpr_no_global le && expr_no_global e
  | Efield (le, _) -> lexpr_no_global le
  | Ederef e -> expr_no_global e

let rec cmd_no_global c =
  match c.cmd with
  | Cskip -> true
  | Cseq (c1, c2) -> cmd_no_global c1 && cmd_no_global c2
  | Cdef (_, _, e) -> expr_no_global e
  | Ccall (_, _, _, _, args) -> List.for_all expr_no_global args
  | Casgn (le, e) -> lexpr_no_global le && expr_no_global e
  | Cif (e, c1, c2) -> expr_no_global e && cmd_no_global c1 && cmd_no_global c2
  | Cwhile (e, c1) -> expr_no_global e && cmd_no_global c1
  | Csection c1 -> cmd_no_global c1
  | Creturn e -> expr_no_global e
  | Cbreak | Ccontinue -> true
  | Cassert e -> expr_no_global e
(*
let rec typ_no_pointer su_env ty =
  match ty with
  | Tunit | Tint _ | Tfloat _ | Tbool _ -> true
  | Tref _ -> false (* the only interesting case *)
  | Tarray (elem_ty, _, _) -> typ_no_pointer su_env elem_ty
  | Tstruct st_name ->
    let st = find_struct su_env st_name in
    List.for_all (fun (field_ty, _) -> typ_no_pointer su_env field_ty) st.struct_fields
*)
let rec expr_call_match pat e =
  match e.expr with
  | Eunit | Ebool _ | Eint _ | Efloat _ | Enull -> true
  | Elexpr le -> lexpr_call_match pat le
  | Eref le -> lexpr_call_match pat le
  | Ebuiltin (f, _) -> pat f (* the only two interest cases *)
  | Earrayinit (_, inits) -> List.for_all (expr_call_match pat) inits
  | Estructinit asgns -> List.for_all (fun (_, e) -> expr_call_match pat e) asgns
and lexpr_call_match pat le =
  match le.lexpr with
  | Evar _ -> true
  | Eindex (le, _, e) -> lexpr_call_match pat le && expr_call_match pat e
  | Efield (le, _) -> lexpr_call_match pat le
  | Ederef e -> expr_call_match pat e

let rec cmd_call_match pat c =
  match c.cmd with
  | Cskip -> true
  | Cseq (c1, c2) -> cmd_call_match pat c1 && cmd_call_match pat c2
  | Cdef (_, _, e) -> expr_call_match pat e
  | Ccall (_, _, _, f, _) -> pat f (* the only two interest cases *)
  | Casgn (le, e) -> lexpr_call_match pat le && expr_call_match pat e
  | Cif (e, c1, c2) -> expr_call_match pat e && cmd_call_match pat c1 && cmd_call_match pat c2
  | Cwhile (e, c1) -> expr_call_match pat e && cmd_call_match pat c1
  | Csection c1 -> cmd_call_match pat c1
  | Creturn e -> expr_call_match pat e
  | Cbreak | Ccontinue -> true
  | Cassert e -> expr_call_match pat e

let pat_BLACKBOX1 funs f =
  if Hashtbl.mem Builtin.builtin_types f then true
  else
    let f_sig = Hashtbl.find funs f in
    match f_sig.funsig_anno with
    | SANDBOX _ -> true
    | _ -> false

let pat_PLOCAL1 funs f =
  if f = "verifier_rand" || f = "prover_rand" then false
  else if Hashtbl.mem Builtin.builtin_types f then true
  else
    let f_sig = Hashtbl.find funs f in
    match f_sig.funsig_anno with
    | SANDBOX _ -> true
    | _ -> false

let pat_BLACKBOX2 funs f =
  if Hashtbl.mem Builtin.builtin_types f then true
  else
    let f_sig = Hashtbl.find funs f in
    match f_sig.funsig_anno with
    | SANDBOX _ -> true
    | _ -> false

let pat_PLOCAL2 funs f =
  if f = "verifier_rand" then false
  else if Hashtbl.mem Builtin.builtin_types f then true
  else
    let f_sig = Hashtbl.find funs f in
    match f_sig.funsig_anno with
    | SANDBOX _ -> true
    | _ -> false

let check_sandbox (*su_env*)_ funs fd =
  (* check no global in body, and no pointer in parameters *)
  begin match fd.fun_anno with
  | NORMAL | ATOMIC -> ()
  | _ ->
    if not @@ cmd_no_global fd.fun_body then
      raise (SandboxUseGlobal (fd.fun_name, fd.fun_anno));
    (*
    if not @@ List.for_all (fun (ty, _) -> typ_no_pointer su_env ty) fd.fun_params then
      raise (SandboxParamPointer (fd.fun_name, fd.fun_anno))
    *)
  end;
  (* check internal calls are pure *)
  match fd.fun_anno with
  | NORMAL | ATOMIC -> ()
  | SANDBOX a ->
    match a with
    | BLACKBOX1 ->
      if not @@ cmd_call_match (pat_BLACKBOX1 funs) fd.fun_body then
        raise (SandboxUseGlobal (fd.fun_name, fd.fun_anno));
    | BLACKBOX2 ->
      if not @@ cmd_call_match (pat_BLACKBOX2 funs) fd.fun_body then
        raise (SandboxUseGlobal (fd.fun_name, fd.fun_anno))
    | PLOCAL1 ->
      if not @@ cmd_call_match (pat_PLOCAL1 funs) fd.fun_body then
        raise (SandboxUseGlobal (fd.fun_name, fd.fun_anno))
    | PLOCAL2 ->
      if not @@ cmd_call_match (pat_PLOCAL2 funs) fd.fun_body then
        raise (SandboxUseGlobal (fd.fun_name, fd.fun_anno))
