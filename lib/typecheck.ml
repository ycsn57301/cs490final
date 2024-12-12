open Ast
open Sandbox
(* open Util *)
open Builtin

module StringSet = Set.Make(String)

exception RedefineVar of string
exception RedefineFun of string
exception RedefineStruct of string
exception RedefineField of string
exception UndefinedVar of string
exception UndefinedCustomFun of string
exception UndefinedBuiltinFun of string
exception UndefinedFieldOf of string * string
exception FieldsNotSameStruct of string * string
exception FieldNeedInit of p_expr_node * string
exception ExprNotLExpr of p_expr_node
exception CannotDeref of expr_node
exception RefK1K2 of lexpr_node
exception AssertNotBool of expr_node
exception CannotMatchHint of p_expr_node * typ
exception NeedHint of p_expr_node
(* exception ExprTypeNotEq of expr * typ * typ *)
exception UnmatchBinopType of binop * expr_node * expr_node
exception UnmatchUopType of uop * expr_node
exception CannotReveal of expr_node
exception CannotCommit of expr_node
exception CannotPrint of expr_node
exception CannotDebug of expr_node
exception CallUnmatchedArgsLength of string * int * p_expr_node list
exception CallUnmatchedRetType of string * typ * typ
exception ArrayinitTooLong of int * p_expr_node list
exception AccessIndexOfNonArray of p_expr_node * p_expr_node
exception AccessFieldOfNonStruct of p_expr_node * string
exception PrivateAccessOnlySupportSimpleType of string * typ
(* plocal function related *)
exception ReferringToGlobalVarInPlocalFun of string
exception DerefInPlocalFun of p_expr
exception PrivateOrPointerInPlocalParameter of string * string
exception PrivateExprInPlocalFun of expr_node
exception CallNonPlocalFunWithinPlocalFun of string
exception BranchingNonPubBool of p_expr_node * typ
exception BranchingSeclvlUnmatch of p_expr_node * seclvl * seclvl
exception RevealNonatom of p_expr_node
exception RevalPlocal of p_expr_node
exception CommitNonatom of p_expr_node
exception CommitPublic of p_expr_node
exception TypingFailed
exception TODOTyping
exception FatalInCast of string
exception FatalInTyping of string

let logs_err_endline (text: string) =
  Logs.err @@ fun m -> m "%s" text

type typing_env =
  {
    typing_scopes : (string, typ) Hashtbl.t list;
    typing_fun_name : string;
    typing_ctx_sec : seclvl; (* the security level of a function's context *)
    typing_funs : (string, funsig) Hashtbl.t;
    typing_su_env : struct_union_env;
  }

let string_of_typing_env env =
  let string_of_scope scope =
    "[" ^ Hashtbl.fold (fun var ty s -> string_of_typ ty ^ " " ^ var ^ ", " ^ s) scope "" ^ "]"
  in
  String.concat ", " (List.map string_of_scope env.typing_scopes)

let assert_function_is_defined env f_name =
  if not (Hashtbl.mem env.typing_funs f_name) then begin
    logs_err_endline (f_name ^ " not found");
    raise TypingFailed
  end

(** find the struct definition of a struct name *)
let env_find_struct env st_name =
  find_struct env.typing_su_env st_name

(** Find the struct definition of the fields *)
let env_find_fields env fields =
  (* find the first field's struct *)
  let st_name = find_field env.typing_su_env (List.hd fields) in
  (* all remaining fields must have the same struct *)
  List.iter (fun field ->
    let st_name' = find_field env.typing_su_env field in
    if st_name <> st_name' then
      raise (FieldsNotSameStruct (st_name, st_name'))) (List.tl fields);
  (* return the struct definition *)
  env_find_struct env st_name

let env_add_var env var typ =
  match env.typing_scopes with
  | [] -> raise (FatalInTyping "add var to empty scope")
  | scope :: _ -> Hashtbl.add scope var typ

type var_type =
  | VTglobal of typ
  | VTlocal of typ

(** find var's type in a stack of scopes *)
let typing_var env var =
  let rec find_var_in_scopes scopes =
  match scopes with
  | [] -> raise (UndefinedVar var)
  | scope :: scopes' ->
    try
      let ty = Hashtbl.find scope var in
      if scopes' = [] then VTglobal ty
      else VTlocal ty
    with Not_found -> find_var_in_scopes scopes'
  in
  find_var_in_scopes env.typing_scopes

let var_in_last_scope env var =
  match env.typing_scopes with
  | [] -> false
  | scope :: _ -> Hashtbl.mem scope var
  let abbr_of_publvl = function
  | K0Public -> "k0"
  | K1Public -> "k1"
  | K2Public -> "k2"

let abbr_of_pvtlvl = function
  | K1Private -> "k1"
  | K2Private -> "k2"

let abbr_of_plclvl = function
  | K1Plocal -> "k1"
  | K2Plocal -> "k2"

let abbr_of_seclvl = function
  | Public lvl -> abbr_of_publvl lvl ^ "pub"
  | Private lvl -> abbr_of_pvtlvl lvl ^ "pvt"
  | Plocal lvl -> abbr_of_plclvl lvl ^ "plc"

let abbr_of_typ = function
  | Tint sec -> abbr_of_seclvl sec ^ "_int"
  | Tbool sec -> abbr_of_seclvl sec ^ "_bool"
  | Tfloat sec -> abbr_of_seclvl sec ^ "_float"
  | _ -> raise (FatalInAST "abbr not supported")

exception CannotCastExpr of expr_node * typ

(** Cast an expression to a specific type.
    Casting order: int/float > K0/K1/K2 > pub/pvt/plc *)
let rec cast_to_typ e expected_ty =
  let ty = type_of_expr e in
  (* cast [e] using a builtin cast function *)
  let cast_by new_type f_name =
    mk_expr (Ebuiltin (f_name, [e])) new_type (loc_of_expr e)
  in
  match ty, expected_ty with
  (* int -> float *)
  | Tint sec1, Tfloat _ ->
    let float_e_ty = Tfloat sec1 in
    let float_e = cast_by float_e_ty (abbr_of_typ float_e_ty ^ "_of_int") in
    cast_to_typ float_e expected_ty
  (* K2 -> K1 -> K0 *)
  (* Tint *)
  | Tint (Public l1), Tint (Public l2) when publvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_publvl l1)
  | Tint (Private l1), Tint (Private l2) when pvtlvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_pvtlvl l1)
  | Tint (Plocal l1), Tint (Plocal l2) when plclvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_plclvl l1)
  | Tint (Public l1), Tint (Private l2) when knwlvl_lt (knwlvl_of_publvl l1) (knwlvl_of_pvtlvl l2) ->
    let l2_e_ty = Tint (Public (publvl_of_pvtlvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_publvl l1) in
    cast_to_typ l2_e expected_ty
  | Tint (Public l1), Tint (Plocal l2) when knwlvl_lt (knwlvl_of_publvl l1) (knwlvl_of_plclvl l2) ->
    let l2_e_ty = Tint (Public (publvl_of_plclvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_publvl l1) in
    cast_to_typ l2_e expected_ty
  | Tint (Private l1), Tint (Plocal l2) when knwlvl_lt (knwlvl_of_pvtlvl l1) (knwlvl_of_plclvl l2) ->
    let l2_e_ty = Tint (Private (pvtlvl_of_plclvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_pvtlvl l1) in
    cast_to_typ l2_e expected_ty
  (* Tfloat *)
  | Tfloat (Public l1), Tfloat (Public l2) when publvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_publvl l1)
  | Tfloat (Private l1), Tfloat (Private l2) when pvtlvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_pvtlvl l1)
  | Tfloat (Plocal l1), Tfloat (Plocal l2) when plclvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_plclvl l1)
  | Tfloat (Public l1), Tfloat (Private l2) when knwlvl_lt (knwlvl_of_publvl l1) (knwlvl_of_pvtlvl l2) ->
    let l2_e_ty = Tfloat (Public (publvl_of_pvtlvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_publvl l1) in
    cast_to_typ l2_e expected_ty
  | Tfloat (Public l1), Tfloat (Plocal l2) when knwlvl_lt (knwlvl_of_publvl l1) (knwlvl_of_plclvl l2) ->
    let l2_e_ty = Tfloat (Public (publvl_of_plclvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_publvl l1) in
    cast_to_typ l2_e expected_ty
  | Tfloat (Private l1), Tfloat (Plocal l2) when knwlvl_lt (knwlvl_of_pvtlvl l1) (knwlvl_of_plclvl l2) ->
    let l2_e_ty = Tfloat (Private (pvtlvl_of_plclvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_pvtlvl l1) in
    cast_to_typ l2_e expected_ty
  (* Tbool *)
  | Tbool (Public l1), Tbool (Public l2) when publvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_publvl l1)
  | Tbool (Private l1), Tbool (Private l2) when pvtlvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_pvtlvl l1)
  | Tbool (Plocal l1), Tbool (Plocal l2) when plclvl_lt l1 l2 ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_" ^ abbr_of_plclvl l1)
  | Tbool (Public l1), Tbool (Private l2) when knwlvl_lt (knwlvl_of_publvl l1) (knwlvl_of_pvtlvl l2) ->
    let l2_e_ty = Tbool (Public (publvl_of_pvtlvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_publvl l1) in
    cast_to_typ l2_e expected_ty
  | Tbool (Public l1), Tbool (Plocal l2) when knwlvl_lt (knwlvl_of_publvl l1) (knwlvl_of_plclvl l2) ->
    let l2_e_ty = Tbool (Public (publvl_of_plclvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_publvl l1) in
    cast_to_typ l2_e expected_ty
  | Tbool (Private l1), Tbool (Plocal l2) when knwlvl_lt (knwlvl_of_pvtlvl l1) (knwlvl_of_plclvl l2) ->
    let l2_e_ty = Tbool (Private (pvtlvl_of_plclvl l2)) in
    let l2_e = cast_by l2_e_ty (abbr_of_typ l2_e_ty ^ "_of_" ^ abbr_of_pvtlvl l1) in
    cast_to_typ l2_e expected_ty
  (* pub -> pvt, pub -> plc, pvt -> plc *)
  | Tint (Public _), Tint (Private _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pub")
  | Tint (Public _), Tint (Plocal _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pub")
  | Tint (Private _), Tint (Plocal _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pvt")
  | Tfloat (Public _), Tfloat (Private _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pub")
  | Tfloat (Public _), Tfloat (Plocal _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pub")
  | Tfloat (Private _), Tfloat (Plocal _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pvt")
  | Tbool (Public _), Tbool (Private _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pub")
  | Tbool (Public _), Tbool (Plocal _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pub")
  | Tbool (Private _), Tbool (Plocal _) ->
    cast_by expected_ty (abbr_of_typ expected_ty ^ "_of_pvt")
  (* TODO: may need to cast ref? *)
  | _, _ when ty = expected_ty -> e
  | _, _ -> raise (CannotCastExpr (e, expected_ty))

let is_K0_lexpr_node le =
  match le.lexpr with
  | Evar _ -> true
  | Eindex (_, sec, _) -> sec = Public K0Public
  | Efield _ -> true
  (* the dereferenced expression must have been type-checked, so it must be a K0 pointer *)
  | Ederef _ -> true

let rec typing_expr env ?(hint = None) pe =
  let extract_hint () =
    match hint with
    | None -> raise (NeedHint pe)
    | Some ty -> ty
  in
  let ret e ty = mk_expr e ty (loc_of_p_expr pe) in
  let e = match pe.p_expr with
  | PEunit -> ret Eunit Tunit
  | PEbool b -> ret (Ebool b) (Tbool (Public K0Public))
  | PEint n -> ret (Eint n) (Tint (Public K0Public))
  | PEfloat f -> ret (Efloat f) (Tfloat (Public K0Public))
  | PEnull ->
    let null_ty = match extract_hint () with
    | (Tref ty) -> Tref ty
    | ty -> raise (CannotMatchHint (pe, ty))
    in
    ret Enull null_ty
  | PEarrayinit pe_inits ->
    let array_ty = extract_hint () in
    begin match array_ty with
    (* TODO: must sure access klvl <= element klvl *)
    (* publicly accessible array *)
    | Tarray (elem_ty, sec, size) ->
      if size < List.length pe_inits then
        raise (ArrayinitTooLong (size, pe_inits));
      let e_inits = List.map (fun pe_init -> typing_expr env ~hint:(Some elem_ty) pe_init) pe_inits in
      ret (Earrayinit (sec, e_inits)) array_ty
    | _ -> raise (CannotMatchHint (pe, array_ty))
    end
  | PEstructinit pe_asgns ->
    let struct_ty = extract_hint () in
    let st = match struct_ty with
    | Tstruct st_name -> env_find_struct env st_name
    | _ -> raise (CannotMatchHint (pe, struct_ty))
    in
    (* all fields must be initialized *)
    List.iter (fun (_, field) ->
      if List.for_all (fun (field', _) -> field <> field') pe_asgns then
        raise (FieldNeedInit (pe, field))
      ) st.struct_fields;
    (* typecheck each asgn *) (* TODO: reorder fields to match the struct's type *)
    let e_asgns = List.map (fun (field, pe_field) ->
      (* find field type from struct definition *)
      let expected_ty, _ = List.find (fun (_, field') -> field = field') st.struct_fields in
      (* type check field *)
      let e_field = typing_expr env ~hint:(Some expected_ty) pe_field in
      (field, e_field)) pe_asgns in
    ret (Estructinit e_asgns) struct_ty
  | PEcall (f, args) ->
    begin match f with
    | "reveal" -> typing_reveal env ret args
    | "print" -> typing_print env ret args
    | "debug0" -> typing_debug0 env ret args
    | "debug1" -> typing_debug1 env ret args
    | "commit" -> typing_commit env ret args
    | _ ->
      let res_ty, e_args = typing_builtin_call env f args in
      ret (Ebuiltin (f, e_args)) res_ty
    end
  | PEbinary (pe1, op, pe2) -> begin
    let op_name = name_of_binop op in
    let e1 = typing_expr env pe1 in
    let e2 = typing_expr env pe2 in
    let ty1 = type_of_expr e1 in
    let ty2 = type_of_expr e2 in
    (* takes in the security levels of two arguments, and two type constructors *)
    let cast_binop sec1 sec2 targ tres =
      let joint_sec = seclvl_join sec1 sec2 in
      let arg_ty = targ joint_sec in
      let res_ty = tres joint_sec in
      ret (Ebuiltin (abbr_of_typ arg_ty^"_"^op_name, [cast_to_typ e1 arg_ty; cast_to_typ e2 arg_ty])) res_ty
    in
    match op with
    (* both operands must be int *)
    | Omod | Oland | Olor | Olxor | Olsl | Olsr -> begin
      match ty1, ty2 with
      | Tint sec1, Tint sec2 ->
        cast_binop sec1 sec2 functor_Tint functor_Tint
      | _, _ -> raise (UnmatchBinopType (op, e1, e2))
    end
    (* both operands must be int or float *)
    | Oadd | Osub | Omul | Odiv -> begin
      match ty1, ty2 with
      (* int + int *)
      | Tint sec1, Tint sec2 ->
        cast_binop sec1 sec2 functor_Tint functor_Tint
      (* float + float / float + int / int + float *)
      | Tfloat sec1, Tfloat sec2
      | Tfloat sec1, Tint sec2
      | Tint sec1, Tfloat sec2 ->
        cast_binop sec1 sec2 functor_Tfloat functor_Tfloat
      (* others *)
      | _, _ -> raise (UnmatchBinopType (op, e1, e2))
      end
    (* both operands must be int or float *)
    | Oge | Ogt | Ole | Olt -> begin
      match ty1, ty2 with
      (* int > int *)
      | Tint sec1, Tint sec2 ->
        cast_binop sec1 sec2 functor_Tint functor_Tbool
      (* float > float / int > float / float > int *)
      | Tfloat sec1, Tfloat sec2
      | Tfloat sec1, Tint sec2
      | Tint sec1, Tfloat sec2 ->
        cast_binop sec1 sec2 functor_Tfloat functor_Tbool
      (* others *)
      | _, _ -> raise (UnmatchBinopType (op, e1, e2))
      end
    (* both operands must be bool *)
    | Oand | Oor -> begin
      match ty1, ty2 with
      (* bool = bool *)
      | Tbool sec1, Tbool sec2 ->
        cast_binop sec1 sec2 functor_Tbool functor_Tbool
      (* others *)
      | _, _ -> raise (UnmatchBinopType (op, e1, e2))
      end
    (* both operands must be atomic *)
    | Oeq | One -> begin
      match ty1, ty2 with
      (* bool = bool *)
      | Tbool sec1, Tbool sec2 ->
        cast_binop sec1 sec2 functor_Tbool functor_Tbool
      (* int = int *)
      | Tint sec1, Tint sec2 ->
        cast_binop sec1 sec2 functor_Tint functor_Tbool
      (* float = float / int = float / float = int *)
      | Tfloat sec1, Tfloat sec2
      | Tfloat sec1, Tint sec2
      | Tint sec1, Tfloat sec2 ->
        cast_binop sec1 sec2 functor_Tfloat functor_Tbool
      (* others *)
      | _, _ -> raise (UnmatchBinopType (op, e1, e2))
      end
    end
  | PEunary (op, pe1) ->
    let op_name = name_of_uop op in
    let e1 = typing_expr env pe1 in
    let ty1 = type_of_expr e1 in
    let cast_uop sec1 targ tres =
      let arg_ty = targ sec1 in
      let res_ty = tres sec1 in
      ret (Ebuiltin (abbr_of_typ arg_ty^"_"^op_name, [cast_to_typ e1 arg_ty])) res_ty
    in
    begin
    match op with
    (* operand must be int *)
    | Olnot -> begin
      match ty1 with
      | Tint sec1 -> cast_uop sec1 functor_Tint functor_Tint
      | _ -> raise (UnmatchUopType (op, e1))
      end
    (* operand must be int or float *)
    | Oneg -> begin
      match ty1 with
      | Tint sec1 -> cast_uop sec1 functor_Tint functor_Tint
      | Tfloat sec1 -> cast_uop sec1 functor_Tfloat functor_Tfloat
      | _ -> raise (UnmatchUopType (op, e1))
      end
    (* operand must be bool *)
    | Onot -> begin
      match ty1 with
      | Tbool sec1 -> cast_uop sec1 functor_Tbool functor_Tbool
      | _ -> raise (UnmatchUopType (op, e1))
      end
    end
  | PEref ple ->
    let le = typing_lexpr env ple in
    (* should not ref to a K1/K2 location as all references must be public. *)
    if not @@ is_K0_lexpr_node le then
      raise (RefK1K2 le);
    ret (Eref le) (Tref (type_of_lexpr le))
  (* The remaining cases are lexpr *)
  | _ ->
    let le = typing_lexpr env pe in
    ret (Elexpr le) (type_of_lexpr le)
  in
  (* Double check the result matches with hint, but this may not be necessary. *)
  let final_e = match hint with
  | None -> e
  | Some ty_hint ->
    cast_to_typ e ty_hint
  in
  final_e

and typing_lexpr env ple =
  let ret le ty = mk_lexpr le ty (loc_of_p_expr ple) in
  match ple.p_expr with
  | PEvar v -> begin
    match typing_var env v with
    | VTlocal ty -> ret (Evar (v, false)) ty
    | VTglobal ty -> ret (Evar (v, true)) ty
    end
  | PEindex (ple_arr, pe_index) ->
    let le_arr = typing_lexpr env ple_arr in
    begin match type_of_lexpr le_arr with
    | Tarray (elem_ty, sec, _) ->
      (* index's security level <= access security level *)
      let ty_index = Tint sec in
      let e_index = typing_expr env ~hint:(Some ty_index) pe_index in
      ret (Eindex (le_arr, sec, e_index)) elem_ty
    | _ -> raise (AccessIndexOfNonArray (ple_arr, pe_index))
    end
  | PEfield (ple_st, field) ->
    (* find struct's type *)
    let le_st = typing_lexpr env ple_st in
    begin match type_of_lexpr le_st with
    | Tstruct st_name ->
      let st = env_find_struct env st_name in
      begin try
        (* find field's type *)
        let field_ty, _ = List.find (fun (_, field') -> field = field') st.struct_fields in
        ret (Efield (le_st, field)) field_ty
      with Not_found -> raise (UndefinedFieldOf (st_name, field))
      end
    | _ -> raise (AccessFieldOfNonStruct (ple_st, field))
    end
  | PEderef pe1 ->
    let e1 = typing_expr env pe1 in begin
      (* e1 must be a reference *)
      match type_of_expr e1 with
      | Tref ty1_base -> ret (Ederef e1) ty1_base
      | _ -> raise (CannotDeref e1)
    end
  | _ -> raise (ExprNotLExpr ple)

(** Reveal pvt to pub *)
and typing_reveal env ret args =
  match args with
  | [arg] ->
    let e_arg = typing_expr env arg in
    begin match type_of_expr e_arg with
    | Tint (Private l) ->
      let pub_ty = Tint (Public (publvl_of_pvtlvl l)) in
      ret (Ebuiltin (abbr_of_typ pub_ty^"_of_pvt", [e_arg])) pub_ty
    | Tfloat (Private l) ->
      let pub_ty = Tfloat (Public (publvl_of_pvtlvl l)) in
      ret (Ebuiltin (abbr_of_typ pub_ty^"_of_pvt", [e_arg])) pub_ty
    | Tbool (Private l) ->
      let pub_ty = Tbool (Public (publvl_of_pvtlvl l)) in
      ret (Ebuiltin (abbr_of_typ pub_ty^"_of_pvt", [e_arg])) pub_ty
    | Tint (Public _) -> e_arg
    | Tfloat (Public _) -> e_arg
    | Tbool (Public _) -> e_arg
    | Tint (Plocal _)
    | Tfloat (Plocal _)
    | Tbool (Plocal _) -> raise (RevalPlocal arg)
    | _ -> raise (RevealNonatom arg)
    end
  | _ -> raise (CallUnmatchedArgsLength ("reveal", 1, args))

(** Send plc to pvt *)
and typing_commit env ret args =
  match args with
  | [arg] ->
    let e_arg = typing_expr env arg in
    begin match type_of_expr e_arg with
    | Tint (Plocal l) ->
      let pvt_ty = Tint (Private (pvtlvl_of_plclvl l)) in
      ret (Ebuiltin (abbr_of_typ pvt_ty^"_of_plc", [e_arg])) pvt_ty
    | Tfloat (Plocal l) ->
      let pvt_ty = Tfloat (Private (pvtlvl_of_plclvl l)) in
      ret (Ebuiltin (abbr_of_typ pvt_ty^"_of_plc", [e_arg])) pvt_ty
    | Tbool (Plocal l) ->
      let pvt_ty = Tbool (Private (pvtlvl_of_plclvl l)) in
      ret (Ebuiltin (abbr_of_typ pvt_ty^"_of_plc", [e_arg])) pvt_ty
    | Tint (Private _) -> e_arg
    | Tfloat (Private _) -> e_arg
    | Tbool (Private _) -> e_arg
    | Tint (Public _)
    | Tfloat (Public _)
    | Tbool (Public _) -> raise (CommitPublic arg)
    | _ -> raise (CommitNonatom arg)
    end
  | _ -> raise (CallUnmatchedArgsLength ("send", 1, args))

and typing_print env ret args =
  match args with
  | [arg] ->
    let e_arg = typing_expr env arg in
    let ty_arg = type_of_expr e_arg in
    begin match ty_arg with
    | Tint _ | Tbool _ | Tfloat _ -> (* only support printing primitive type at the moment *)
      ret (Ebuiltin (abbr_of_typ ty_arg^"_print", [e_arg])) Tunit
    | _ -> raise (CannotPrint e_arg)
    end
  | _ -> raise (CallUnmatchedArgsLength ("print", 1, args))

and typing_debug0 env ret args =
  match args with
  | [arg] ->
    let e_arg = typing_expr env arg in
    let ty_arg = type_of_expr e_arg in
    begin match ty_arg with
    | Tint sec | Tbool sec | Tfloat sec when sec = Public K0Public -> (* only support printing primitive type at the moment *)
      ret (Ebuiltin (abbr_of_typ ty_arg^"_debug0", [e_arg])) Tunit
    | _ -> raise (CannotDebug e_arg)
    end
  | _ -> raise (CallUnmatchedArgsLength ("debug0", 1, args))

and typing_debug1 env ret args =
  match args with
  | [arg] ->
    let e_arg = typing_expr env arg in
    let ty_arg = type_of_expr e_arg in
    begin match ty_arg with
    | Tint sec | Tbool sec | Tfloat sec when (* only support printing primitive type at the moment *)
      sec = Public K0Public || sec = Public K1Public || sec = Plocal K1Plocal ->
      ret (Ebuiltin (abbr_of_typ ty_arg^"_debug1", [e_arg])) Tunit
    | _ -> raise (CannotDebug e_arg)
    end
  | _ -> raise (CallUnmatchedArgsLength ("debug1", 1, args))

and typing_call_args env f params_ty args =
  (* args length must match with params length *)
  if List.length args <> List.length params_ty then
    raise (CallUnmatchedArgsLength (f, List.length params_ty, args));
  (* type check and cast all arguments. *)
  let args_casted = List.map2 (fun (param_ty, cc) arg ->
    match cc with
    | CCval -> typing_expr env ~hint:(Some param_ty) arg
    | CCref -> (* convert all call-by-ref before typechecking *)
      let ref_arg = { p_expr = PEref arg; p_expr_loc = loc_of_p_expr arg } in
      typing_expr env ~hint:(Some (Tref param_ty)) ref_arg) params_ty args
  in
  args_casted

(** Return a pair of function's return type and typed arguments *)
and typing_builtin_call env f args =
  (* find function signature *)
  let f_sig =
  try Hashtbl.find builtin_types f
  with Not_found -> raise (UndefinedBuiltinFun f)
  in
  let params_ty = f_sig.funsig_params in
  let ret_ty = f_sig.funsig_return in
  let args_casted = typing_call_args env f params_ty args in
  ret_ty, args_casted

(** Return typed arguments *)
and typing_custom_call env var_ty var_name f args =
  (* check redundancy *)
  if var_in_last_scope env var_name then
    raise (RedefineVar var_name);
  (* find function signature *)
  let f_sig =
    try Hashtbl.find env.typing_funs f
    with Not_found -> raise (UndefinedCustomFun f)
  in
  let params_ty = f_sig.funsig_params in
  let ret_ty = f_sig.funsig_return in
  (* return type must be exactly equal as we can not do casting here *)
  if ret_ty <> var_ty then
    raise (CallUnmatchedRetType (f, ret_ty, var_ty));
  let args_casted = typing_call_args env f params_ty args in
  f_sig.funsig_anno, args_casted

let typing_vardef env v_ty var_name e_init =
  (* check redundancy *)
  if var_in_last_scope env var_name then
    raise (RedefineVar var_name);
  (* match variable's type with initial value *)
  let e_casted = typing_expr env ~hint:(Some v_ty) e_init in
  env_add_var env var_name v_ty;
  e_casted

let typing_gvardef env vd_node =
  let vd = vd_node.p_gvardef in
  { gvardef = {
      gvar_typ = vd.pgvar_typ;
      gvar_name = vd.pgvar_name;
      gvar_init = typing_vardef env vd.pgvar_typ vd.pgvar_name vd.pgvar_init
    };
    gvardef_meta = { gvardef_loc = loc_of_p_gvardef vd_node }
  }

let rec typing_cmd env pc =
  let ret c = mk_cmd c (loc_of_p_cmd pc) in
  match pc.p_cmd with
  | PCskip -> ret Cskip
  | PCseq (pc1, pc2) ->
    let c1 = typing_cmd env pc1 in
    let c2 = typing_cmd env pc2 in
    ret (Cseq (c1, c2))
  | PCdef (v_ty, v, pe) ->
    begin match pe.p_expr with
    | PEcall (f, pe_args) ->
      if Hashtbl.mem env.typing_funs f then begin (* custom call *)
        let anno, e_args = typing_custom_call env v_ty v f pe_args in
        env_add_var env v v_ty;
        ret (Ccall (v_ty, anno, v, f, e_args))
      end
      else (* builtin *)
        ret (Cdef (v_ty, v, typing_vardef env v_ty v pe))
    | _ -> ret (Cdef (v_ty, v, typing_vardef env v_ty v pe))
    end
  | PCasgn (ple, pe) ->
    let le = typing_lexpr env ple in
    let le_ty = type_of_lexpr le in
    let e = typing_expr env ~hint:(Some le_ty) pe in
    ret (Casgn (le, e))
  | PCeval _ ->
    raise (FatalInTyping "PCeval should never appear after rewriting")
  | PCif (pe, pc1, pc2) ->
    let e = typing_expr env pe in
    (* check security level of branching expression *)
    (* XXX: probably move this checking to sandbox.ml *)
    begin match type_of_expr e with
    | Tbool l ->
      if not (seclvl_le l env.typing_ctx_sec) then
        raise (BranchingSeclvlUnmatch (pe, l, env.typing_ctx_sec))
    | ty -> raise (BranchingNonPubBool (pe, ty))
    end;
    let c1 = typing_cmd env pc1 in
    let c2 = typing_cmd env pc2 in
    ret (Cif (e, c1, c2))
  | PCfor _ -> raise (FatalInTyping "PCfor should not exist")
  | PCwhile (pe, pc1) ->
    let e = typing_expr env pe in
    (* check knowledge level of branching expression *)
    begin match type_of_expr e with
    | Tbool l ->
      if not (seclvl_le l env.typing_ctx_sec) then
        raise (BranchingSeclvlUnmatch (pe, l, env.typing_ctx_sec))
    | ty -> raise (BranchingNonPubBool (pe, ty))
    end;
    let c1 = typing_cmd env pc1 in
    ret (Cwhile (e, c1))
  | PCsection pc1 ->
    let new_scope = Hashtbl.create 20 in
    let c1 = typing_cmd { env with typing_scopes = new_scope :: env.typing_scopes } pc1 in
    ret (Csection c1)
  | PCreturn pe ->
    let f = env.typing_fun_name in
    (* this function must be user-defined, so we do not need to lookup the builtin function's table *)
    let expected_ty = (Hashtbl.find env.typing_funs f).funsig_return in
    let e = typing_expr env ~hint:(Some expected_ty) pe in
    ret (Creturn e)
  | PCbreak -> ret Cbreak
  | PCcontinue -> ret Ccontinue
  | PCassert pe ->
    let e = typing_expr env pe in
    match type_of_expr e with
    | Tbool _ -> ret (Cassert e)
    | _ -> raise (AssertNotBool e)

(* Replace all occurrences of variables in refs, like x, to *x. *)
let p_expr_ref2val refs pe =
  let rec convert pe =
    let new_raw_pe = match pe.p_expr with
    | PEunit | PEbool _ | PEint _ | PEfloat _ | PEnull -> pe.p_expr
    | PEref pe1 -> PEref (convert pe1)
    | PEcall (f, args) -> PEcall (f, List.map convert args)
    | PEbinary (pe1, op, pe2) -> PEbinary (convert pe1, op, convert pe2)
    | PEunary (op, pe1) -> PEunary (op, convert pe1)
    | PEarrayinit inits -> PEarrayinit (List.map convert inits)
    | PEstructinit asgns -> PEstructinit (List.map (fun (field, init) -> (field, convert init)) asgns)
    (* The only meaningful case *)
    | PEvar var -> if StringSet.mem var refs then PEderef pe else pe.p_expr
    | PEindex (base, index) -> PEindex (convert base, convert index)
    | PEfield (base, field) -> PEfield (convert base, field)
    | PEderef pe1 -> PEderef (convert pe1)
    in
    { pe with p_expr = new_raw_pe }
  in
  convert pe

(** Replace all occurrences of variables in refs, like x, to *x. *)
let p_cmd_ref2val refs pc =
  let rec convert refs pc =
    let new_refs, new_raw_pc = match pc.p_cmd with
    | PCskip | PCbreak | PCcontinue -> refs, pc.p_cmd
    | PCseq (pc1, pc2) ->
      let refs1, pc1' = convert refs pc1 in
      let refs2, pc2' = convert refs1 pc2 in
      refs2, PCseq (pc1', pc2')
    (* var might overshadow a parameter with the same name. *)
    | PCdef (ty, var, init) ->
      let init' = (p_expr_ref2val refs init) in
      StringSet.remove var refs, PCdef (ty, var, init')
    | PCasgn (ple, pe) -> refs, PCasgn (p_expr_ref2val refs ple, p_expr_ref2val refs pe)
    | PCeval pe -> refs, PCeval (p_expr_ref2val refs pe)
    | PCif (pe, pc1, pc2) -> refs, PCif (p_expr_ref2val refs pe, snd @@ convert refs pc1, snd @@ convert refs pc2)
    | PCfor _ -> raise (FatalInTyping "PCfor should not exist")
    | PCwhile (pe, pc1) -> refs, PCwhile (p_expr_ref2val refs pe, snd @@ convert refs pc1)
    (* the definitions within a section do not interfer with the outside *)
    | PCsection pc1 -> refs, PCsection (snd @@ convert refs pc1)
    | PCreturn pe -> refs, PCreturn (p_expr_ref2val refs pe)
    | PCassert pe -> refs, PCassert (p_expr_ref2val refs pe)
    in
    new_refs, { pc with p_cmd = new_raw_pc }
  in
  snd @@ convert refs pc

let typing_fundef env fd_node =
  let fd = fd_node.p_fundef in
  let new_env = {
    env with
    typing_scopes = Hashtbl.create 20 :: env.typing_scopes;
    typing_fun_name = fd.pfun_name;
    typing_ctx_sec = seclvl_of_fun_anno_kind fd.pfun_anno;
  } in
  (* Convert call-by-reference parameters to call-by-val:
     A parameter int & x will become int* x, and all occurrences of x in
     function body will become *x. *)
  let converted_params = List.map (fun (ty, var, cc) ->
    match cc with
    | CCval -> (ty, var)
    | CCref -> (Tref ty, var)) fd.pfun_params in
  let refs = List.fold_left (fun refs (_, var, cc) ->
    match cc with
    | CCval -> refs
    | CCref -> StringSet.add var refs) StringSet.empty fd.pfun_params in
  let rewritten_body = Rewrite.rewrite_for_to_while fd.pfun_body in
  let converted_body = p_cmd_ref2val refs rewritten_body in
  let extracted_body = Rewrite.extract_funcall env.typing_funs converted_body in
  (* plocal function should not take in arguments containing pvt or pointer *)
  (* if fd.pfun_anno = PLOCAL then
    List.iter (fun (ty, param_name) ->
      if typ_has_pvt_or_pointer env.typing_su_env ty then
        raise (PrivateOrPointerInPlocalParameter (fd.pfun_name, param_name))) converted_params; *)
  (* typing function body *)
  List.iter (fun (ty, var) -> env_add_var new_env var ty) converted_params;
  { fundef = {
      fun_anno = fd.pfun_anno;
      fun_name = fd.pfun_name;
      fun_ret_typ = fd.pfun_ret_typ;
      fun_params = converted_params;
      fun_body = typing_cmd new_env extracted_body
    };
    fundef_meta = { fundef_loc = loc_of_p_fundef fd_node }
  }

(** Scan all definitions to construct a struct/union environment *)
let collect_su_info su_env tops =
  let add_structdef p_sd =
    let sd = {
      struct_name = p_sd.pstruct_name;
      struct_fields = p_sd.pstruct_fields;
    } in
    (* redundancy check of struct *)
    if Hashtbl.mem su_env.su_structs sd.struct_name then
      raise (RedefineStruct sd.struct_name);
    (* redundancy check of fields *)
    List.iter (fun (_, field) ->
      if Hashtbl.mem su_env.su_fields field then
        raise (RedefineField field)) sd.struct_fields;
    (* add struct and fields into env *)
    Hashtbl.add su_env.su_structs sd.struct_name sd;
    List.iter (fun (_, field) ->
      Hashtbl.add su_env.su_fields field sd.struct_name) sd.struct_fields
  in
  (* scan all tops *)
  List.iter (function
  | PTstructdef p_sd -> add_structdef p_sd.p_structdef
  | _ -> ()) tops

let initial_typing_env () =
  let env = { typing_scopes = [Hashtbl.create 40];
              typing_fun_name = "$TOP";
              typing_ctx_sec = Public K0Public;
              typing_funs = Hashtbl.create 40;
              typing_su_env = { su_structs = Hashtbl.create 40; su_fields = Hashtbl.create 40; }; }
  in
  (* Hashtbl.add_seq env.typing_funs builtin_types; *)
  env

let typing_prog ?(env = initial_typing_env ()) ptops =
  try
    (* collect struct definitions *)
    collect_su_info env.typing_su_env ptops;
    (* typecheck struct definitions *)
    (* Hashtbl.iter (fun _ st -> typing_structdef st) env.typing_su_env.su_structs; *)
    (* record function signatures *)
    List.iter (function
    | PTfundef fd_node -> (* normal function *)
      let fd = fd_node.p_fundef in
      if Hashtbl.mem builtin_types fd.pfun_name then
        raise (RedefineFun fd.pfun_name);
      (* TODO: we want to warn about redefine function, but also want to allow define declared functions. *)
      (*
      else if Hashtbl.mem env.typing_funs fd.pfun_name then
        raise (RedefineFun fd.pfun_name);
      *)
      Hashtbl.add env.typing_funs fd.pfun_name (sig_of_p_fundef fd)
    | PTxfundecl xd_node -> (* external function *)
      let xd = xd_node.p_xfundecl in
      if Hashtbl.mem env.typing_funs xd.pxfun_name || Hashtbl.mem builtin_types xd.pxfun_name then
        raise (RedefineFun xd.pxfun_name);
      Hashtbl.add env.typing_funs xd.pxfun_name (sig_of_p_xfundecl xd)
    | _ -> ()) ptops;
    (* typecheck and record global variable definitions *)
    let gvar_defs = List.fold_left (fun gvars pdecl ->
      match pdecl with
      | PTgvardef p_vd -> gvars @ [typing_gvardef env p_vd]
      | _ -> gvars) [] ptops in
    (* type check functions *)
    let fun_defs = List.fold_right (fun pdef defs ->
      match pdef with
      | PTfundef p_fd ->
        let fd = typing_fundef env p_fd in
        check_sandbox env.typing_su_env env.typing_funs fd.fundef;
        fd :: defs
      | _ -> defs)
      ptops [] in
    (* collect extern *)
    let fun_decls = List.fold_right (fun pdef defs ->
      match pdef with
      | PTxfundecl xd_node ->
        xd_node.p_xfundecl :: defs
      | _ -> defs)
      ptops [] in
    gvar_defs, fun_defs, fun_decls, env
  with
  | RedefineVar var ->
    logs_err_endline ("Redefine variable " ^ var);
    raise TypingFailed
  | RedefineFun f ->
    logs_err_endline ("Redefine function " ^ f);
    raise TypingFailed
  | UndefinedVar var ->
    logs_err_endline ("Refering to undefined variable " ^ var);
    raise TypingFailed
  | UndefinedCustomFun f ->
    logs_err_endline ("Calling undefined custom function " ^ f);
    raise TypingFailed
  | UndefinedBuiltinFun f ->
    logs_err_endline ("Calling undefined builtin function " ^ f);
    raise TypingFailed
  | ExprNotLExpr ple ->
    logs_err_endline ("Expression " ^ string_of_p_expr_node ple ^ "should be L-expression");
    raise TypingFailed
  | RefK1K2 le ->
    Logs.err (fun m -> m "L-expression %s of non-K1 access can not be referred by a pointer"
      (string_of_lexpr_node le));
    raise TypingFailed
  | AssertNotBool e ->
    Logs.err (fun m -> m "Assertion %s's type is %s rather than bool"
      (string_of_expr_node e) (string_of_typ @@ type_of_expr e));
    raise TypingFailed
  (* | ExprTypeNotEq (e, e_ty, expected_ty) ->
    logs_err_endline (Printf.sprintf "Expression %s's type %s should be %s"
      (string_of_expr e) (string_of_typ e_ty) (string_of_typ expected_ty));
    raise TypingFailed *)
  | UnmatchBinopType (op, e1, e2) ->
    Logs.err (fun m -> m "Binary operation %s is incompatible with its operands %s of type %s and %s of type %s"
      (string_of_binop op) (string_of_expr_node e1) (string_of_typ @@ type_of_expr e1) (string_of_expr_node e2) (string_of_typ @@ type_of_expr e2));
    raise TypingFailed
  | UnmatchUopType (op, e1) ->
    Logs.err (fun m -> m "Unary operation %s is incompatible with its operand %s of type %s"
      (string_of_uop op) (string_of_expr_node e1) (string_of_typ @@ type_of_expr e1));
    raise TypingFailed
  | CallUnmatchedArgsLength (f, len, args) ->
    Logs.err (fun m -> m "Function call %s(%s) is expecting %s arguments"
      f (String.concat ", " @@ List.map string_of_p_expr_node args) (string_of_int len));
    raise TypingFailed
  | AccessIndexOfNonArray (ple_arr, pe_index) ->
    Logs.err (fun m -> m "Access index %s of non-array %s"
      (string_of_p_expr_node pe_index) (string_of_p_expr_node ple_arr));
    raise TypingFailed
  | ArrayinitTooLong (size, pe_inits) ->
    Logs.err (fun m -> m "Array of size %d can not be initialized with an oversized init list {%s}"
      size (String.concat ", " (List.map string_of_p_expr_node pe_inits)));
    raise TypingFailed
  | CannotCastExpr (e, expected_ty) ->
    Logs.err (fun m -> m "Expression %s of type %s can not be casted to %s"
      (string_of_expr e.expr) (string_of_typ (type_of_expr e)) (string_of_typ expected_ty));
    raise TypingFailed
  | CannotDeref e ->
    Logs.err (fun m -> m "Can not deref %s of type %s"
      (string_of_expr_node e) (string_of_typ @@ type_of_expr e));
    raise TypingFailed
  | CannotMatchHint (pe, ty) ->
    Logs.err (fun m -> m "Expression %s can not be casted to match typing hint %s"
      (string_of_p_expr_node pe) (string_of_typ ty));
    raise TypingFailed
  | BranchingSeclvlUnmatch (pe, sec, max_sec) ->
    Logs.err (fun m -> m "Branching expression %s of security level %s should be no more than max level %s"
      (string_of_p_expr_node pe) (string_of_seclvl sec) (string_of_seclvl max_sec));
    raise TypingFailed
