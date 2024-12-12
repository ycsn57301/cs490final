open Ast
(* open Util *)

exception TODOGen
exception UnsupportedBuiltin of string
exception FatalInGen of string

type zk_party =
  | PROVER
  | VERIFIER

(*
type empgen_env = {
  empgen_su_env : struct_union_env;
  empgen_gvars : gvardef_node list;
}
*)
(** This is used when refering to a variable as an lvalue. *)
let emp_lname_of_alias = function
  | AliasNorm (var, n) -> Printf.sprintf "ctx->__%s_%d" var n
  | AliasGlob var -> "(*" ^ var ^ ")"

(** This is used when defining a variable of this alias. *)
let emp_name_of_alias = function
| AliasNorm (var, n) -> "__" ^ var ^ "_" ^ string_of_int n
| AliasGlob var -> var

(** The type that has unique_ptr<...> *)
let rec emp_of_typ = function
  | Tarray (_, Public _, _)
  | Tarray (_, Plocal _, _) as arr_ty -> Printf.sprintf "std::unique_ptr<%s>" (emp_of_raw_typ arr_ty)
  | Tarray (_, Private _, _ ) -> raise TODOGen
  | ty -> emp_of_raw_typ ty

(** The type used in unique_ptr<...> *)
and emp_of_raw_typ = function
  | Tunit -> "void"
  | Tbool (Private _) -> "Bit"
  | Tbool (Public _) -> "bool"
  | Tbool (Plocal _) -> "bool"
  | Tint (Private _) -> "Integer"
  | Tint (Public _) -> "int"
  | Tint (Plocal _) -> "int"
  | Tfloat (Private _) -> "Float"
  | Tfloat (Public _) -> "float"
  | Tfloat (Plocal _) -> "float"
  | Tarray (ty, Public _, size)
  | Tarray (ty, Plocal _, size) -> Printf.sprintf "array<%s, %d>" (emp_of_typ ty) size
  | Tarray (_, Private _, _ ) -> raise TODOGen
  | Tstruct st_name -> st_name
  | Tref ty -> emp_of_typ ty ^ " *"

let emp_of_param_typ = function
  | Tarray (_, Public _, _)
  | Tarray (_, Plocal _, _) as arr_ty -> emp_of_typ arr_ty ^ " &"
  | Tarray (_, Private _, _ ) -> raise TODOGen
  | ty -> emp_of_typ ty

let rec emp_of_value = function
  | Vunit -> raise (FatalInGen "can not define Vunit in EMP")
  | Vint i -> string_of_int i
  | Vfloat f -> Printf.sprintf "%f" f
  | Vbool b -> string_of_bool b
  | Vref lv -> "& (" ^ emp_of_lvalue lv ^ ")"
  | Vnull -> "nullptr"
  | Varray _ -> raise (FatalInGen "can not define Varray in EMP")
  | Vstruct st ->
    let asgns = Hashtbl.fold (fun _ v asgns' -> (emp_of_value v) :: asgns') st [] in
    "{" ^ String.concat ", " asgns ^ "}"
and emp_of_lvalue lv =
  match lv.lvalue with
  | Vvar var -> emp_lname_of_alias var
  | Vindex (arr, _, index) -> Printf.sprintf "(*(%s))[%s]" (emp_of_lvalue arr) (string_of_int index)
  | Vfield (st, field) -> emp_of_lvalue st ^ "." ^ field

let rec emp_default_value su_env ty =
  match ty with
  | Tunit -> ""
  | Tbool (Private _) -> "Bit(false, ALICE)"
  | Tbool (Public _) -> "false"
  | Tbool (Plocal _) -> "false"
  | Tint (Private _) -> "Integer(32, 0, ALICE)"
  | Tint (Public _) -> "0"
  | Tint (Plocal _) -> "0"
  | Tfloat (Private _) -> "Float(0, ALICE)"
  | Tfloat (Public _) -> "0"
  | Tfloat (Plocal _) -> "0"
  | Tarray (_, Public _, _)
  | Tarray (_, Plocal _, _) ->
    Printf.sprintf "std::make_unique<%s>()" (emp_of_raw_typ ty)
    (*
    let elem_text = emp_default_value su_env ty_elem in
    "{" ^ String.concat ", " (list_repeat elem_text size) ^ "}"
    *)
  | Tarray (_, Private _, _) -> raise TODOGen
  | Tstruct st_name ->
    let st = find_struct su_env st_name in
    let asgns = List.map (fun (ty_field, _) -> emp_default_value su_env ty_field) st.struct_fields in
    "{" ^ String.concat ", " asgns ^ "}"
  | Tref _ -> "nullptr"

let rec emp_of_typed_value party tv =
  match tv with
  | TVunit -> raise (FatalInGen "Can not generate TVunit")
  | TVint (sec, i) ->
    let text = string_of_int i in
    begin match sec with
    | Public _ -> text
    | Plocal _ -> if party = PROVER then text else "0"
    | Private _ -> if party = PROVER then "Integer(32, " ^ text ^ ", ALICE)" else "Integer(32, 0, ALICE)"
    end
  | TVbool (sec, b) ->
    let text = string_of_bool b in
    begin match sec with
    | Public _ -> text
    | Plocal _ -> if party = PROVER then text else "false"
    | Private _ -> if party = PROVER then "Bit(" ^ text ^ ", ALICE)" else "Bit(false, ALICE)"
    end
  | TVfloat (sec, f) ->
    let text = Printf.sprintf "%f" f in
    begin match sec with
    | Public _ -> text
    | Plocal _ -> if party = PROVER then text else "0"
    | Private _ -> if party = PROVER then "Float(" ^ text ^ ", ALICE)" else "Float(0, ALICE)"
    end
  | TVref lv -> "& (" ^ emp_of_lvalue lv ^ ")"
  | TVnull -> "nullptr"
  | TVarray (ty_elem, sec, size, arr) ->
    begin match sec with
    | Private _ -> raise (FatalInGen "Can not generate private array")
    | Public _ | Plocal _ ->
      let text_typ = Printf.sprintf "array<%s, %d>" (emp_of_typ ty_elem) size in
      let text_inits = String.concat ", " (List.of_seq (Seq.map (fun tv_elem ->
        emp_of_typed_value party tv_elem
      ) (Array.to_seq arr))) in
      Printf.sprintf "std::make_unique<%s>(%s{%s})" text_typ text_typ text_inits
    end
  | TVstruct map ->
    let asgns = List.of_seq (Seq.map (fun (field, tv_field) ->
      Printf.sprintf ".%s = %s" field (emp_of_typed_value party tv_field)
    ) (StringMap.to_seq map)) in
    "{" ^ String.concat ", " asgns ^ "}"

let emp_of_builtin _ (* party *) f args =
  match f, args with
  | "pi", [] -> "M_PI"
  | "verifier_rand", [a1; a2] -> "OU_verifier_rand(" ^ a1 ^ ", " ^ a2 ^ ")"
  | "prover_rand", [a1; a2] -> "OU_prover_rand(" ^ a1 ^ ", " ^ a2 ^ ")"

  (* cast *)
  | "k1pvt_float_of_int", [_]
  | "k2pvt_float_of_int", [_] -> raise (UnsupportedBuiltin f)
  | "k0pub_float_of_int", [a1]
  | "k1pub_float_of_int", [a1]
  | "k2pub_float_of_int", [a1]
  | "k1plc_float_of_int", [a1]
  | "k2plc_float_of_int", [a1] -> "float" ^ a1
  
  | "k1pvt_int_of_pub", [a1]
  | "k2pvt_int_of_pub", [a1] -> Printf.sprintf "Integer(32, %s, ALICE)" a1
  | "k1pvt_float_of_pub", [a1]
  | "k2pvt_float_of_pub", [a1] -> Printf.sprintf "Float(%s, ALICE)" a1
  | "k1pvt_bool_of_pub", [a1]
  | "k2pvt_bool_of_pub", [a1] -> Printf.sprintf "Bit(%s, ALICE)" a1

  | "k1pub_int_of_pvt", [a1]
  | "k2pub_int_of_pvt", [a1] -> Printf.sprintf "%s.reveal<int>(PUBLIC)" a1
  | "k1pub_float_of_pvt", [a1]
  | "k2pub_float_of_pvt", [a1] -> Printf.sprintf "%s.reveal<double>(PUBLIC)" a1
  | "k1pub_bool_of_pvt", [a1]
  | "k2pub_bool_of_pvt", [a1] -> Printf.sprintf "%s.reveal<bool>(PUBLIC)" a1

  | "k1pvt_int_of_plc", [a1]
  | "k2pvt_int_of_plc", [a1] -> Printf.sprintf "Integer(32, %s, ALICE)" a1
  | "k1pvt_float_of_plc", [a1]
  | "k2pvt_float_of_plc", [a1] -> Printf.sprintf "Float(%s, ALICE)" a1
  | "k1pvt_bool_of_plc", [a1]
  | "k2pvt_bool_of_plc", [a1] -> Printf.sprintf "Bit(%s, ALICE)" a1

  (* FIXME: does this work on verifier side? *)
  | "k1plc_int_of_pvt", [a1]
  | "k2plc_int_of_pvt", [a1] -> Printf.sprintf "%s.reveal<int>(ALICE)" a1
  | "k1plc_float_of_pvt", [a1]
  | "k2plc_float_of_pvt", [a1] -> Printf.sprintf "%s.reveal<double>(ALICE)" a1
  | "k1plc_bool_of_pvt", [a1]
  | "k2plc_bool_of_pvt", [a1] -> Printf.sprintf "%s.reveal<bool>(ALICE)" a1

  | "k1plc_int_of_pub", [a1]
  | "k2plc_int_of_pub", [a1] -> a1
  | "k1plc_float_of_pub", [a1]
  | "k2plc_float_of_pub", [a1] -> a1
  | "k1plc_bool_of_pub", [a1]
  | "k2plc_bool_of_pub", [a1] -> a1

  | "k1pub_int_of_k0", [a1] -> a1
  | "k2pub_int_of_k0", [a1] -> a1
  | "k2pub_int_of_k1", [a1] -> a1
  | "k2pvt_int_of_k1", [a1] -> a1
  | "k2plc_int_of_k1", [a1] -> a1

  | "k1pub_float_of_k0", [a1] -> a1
  | "k2pub_float_of_k0", [a1] -> a1
  | "k2pub_float_of_k1", [a1] -> a1
  | "k2pvt_float_of_k1", [a1] -> a1
  | "k2plc_float_of_k1", [a1] -> a1

  | "k1pub_bool_of_k0", [a1] -> a1
  | "k2pub_bool_of_k0", [a1] -> a1
  | "k2pub_bool_of_k1", [a1] -> a1
  | "k2pvt_bool_of_k1", [a1] -> a1
  | "k2plc_bool_of_k1", [a1] -> a1

  | _ ->
    match String.sub f 2 (String.length f - 2), args with (* treat K0~K2 the same *)
    (* int *)
    | "pvt_int_add", [a1;a2] -> a1 ^ " + " ^ a2
    | "pvt_int_sub", [a1;a2] -> a1 ^ " - " ^ a2
    | "pvt_int_mul", [a1;a2] -> a1 ^ " * " ^ a2
    | "pvt_int_div", [a1;a2] -> a1 ^ " / " ^ a2
    | "pvt_int_mod", [a1;a2] -> a1 ^ " % " ^ a2
    | "pvt_int_lor", [a1;a2] -> a1 ^ " | " ^ a2
    | "pvt_int_lsl", [a1;a2] -> a1 ^ " << " ^ a2
    | "pvt_int_lsr", [a1;a2] -> a1 ^ " >> " ^ a2
    | "pvt_int_land", [a1;a2] -> a1 ^ " & " ^ a2
    | "pvt_int_lxor", [a1;a2] -> a1 ^ " ^ " ^ a2
    | "pvt_int_ge", [a1;a2] -> a1 ^ " >= " ^ a2
    | "pvt_int_gt", [a1;a2] -> a1 ^ " > " ^ a2
    | "pvt_int_le", [a1;a2] -> a1 ^ " <= " ^ a2
    | "pvt_int_lt", [a1;a2] -> a1 ^ " < " ^ a2
    | "pvt_int_eq", [a1;a2] -> a1 ^ " == " ^ a2
    | "pvt_int_ne", [a1;a2] -> a1 ^ " != " ^ a2
    | "pvt_int_lnot", [a1] -> "~ " ^ a1
    | "pvt_int_neg", [a1] -> "- " ^ a1

    | "pub_int_add", [a1;a2] -> a1 ^ " + " ^ a2
    | "pub_int_sub", [a1;a2] -> a1 ^ " - " ^ a2
    | "pub_int_mul", [a1;a2] -> a1 ^ " * " ^ a2
    | "pub_int_div", [a1;a2] -> a1 ^ " / " ^ a2
    | "pub_int_mod", [a1;a2] -> a1 ^ " % " ^ a2
    | "pub_int_lor", [a1;a2] -> a1 ^ " | " ^ a2
    | "pub_int_lsl", [a1;a2] -> a1 ^ " << " ^ a2
    | "pub_int_lsr", [a1;a2] -> a1 ^ " >> " ^ a2
    | "pub_int_land", [a1;a2] -> a1 ^ " & " ^ a2
    | "pub_int_lxor", [a1;a2] -> a1 ^ " ^ " ^ a2
    | "pub_int_ge", [a1;a2] -> a1 ^ " >= " ^ a2
    | "pub_int_gt", [a1;a2] -> a1 ^ " > " ^ a2
    | "pub_int_le", [a1;a2] -> a1 ^ " <= " ^ a2
    | "pub_int_lt", [a1;a2] -> a1 ^ " < " ^ a2
    | "pub_int_eq", [a1;a2] -> a1 ^ " == " ^ a2
    | "pub_int_ne", [a1;a2] -> a1 ^ " != " ^ a2
    | "pub_int_lnot", [a1] -> "~ " ^ a1
    | "pub_int_neg", [a1] -> "- " ^ a1
    
    | "plc_int_add", [a1;a2] -> a1 ^ " + " ^ a2
    | "plc_int_sub", [a1;a2] -> a1 ^ " - " ^ a2
    | "plc_int_mul", [a1;a2] -> a1 ^ " * " ^ a2
    | "plc_int_div", [a1;a2] -> a1 ^ " / " ^ a2
    | "plc_int_mod", [a1;a2] -> a1 ^ " % " ^ a2
    | "plc_int_lor", [a1;a2] -> a1 ^ " | " ^ a2
    | "plc_int_lsl", [a1;a2] -> a1 ^ " << " ^ a2
    | "plc_int_lsr", [a1;a2] -> a1 ^ " >> " ^ a2
    | "plc_int_land", [a1;a2] -> a1 ^ " & " ^ a2
    | "plc_int_lxor", [a1;a2] -> a1 ^ " ^ " ^ a2
    | "plc_int_ge", [a1;a2] -> a1 ^ " >= " ^ a2
    | "plc_int_gt", [a1;a2] -> a1 ^ " > " ^ a2
    | "plc_int_le", [a1;a2] -> a1 ^ " <= " ^ a2
    | "plc_int_lt", [a1;a2] -> a1 ^ " < " ^ a2
    | "plc_int_eq", [a1;a2] -> a1 ^ " == " ^ a2
    | "plc_int_ne", [a1;a2] -> a1 ^ " != " ^ a2
    | "plc_int_lnot", [a1] -> "~ " ^ a1
    | "plc_int_neg", [a1] -> "- " ^ a1
    
    (* float *)
    | "pvt_float_add", [a1;a2] -> a1 ^ " + " ^ a2
    | "pvt_float_sub", [a1;a2] -> a1 ^ " - " ^ a2
    | "pvt_float_mul", [a1;a2] -> a1 ^ " * " ^ a2
    | "pvt_float_div", [a1;a2] -> a1 ^ " / " ^ a2
    | "pvt_float_ge", [a1;a2] -> a2 ^ ".less_equal(" ^ a1 ^ ")"
    | "pvt_float_gt", [a1;a2] -> a2 ^ ".less_than(" ^ a1 ^ ")"
    | "pvt_float_le", [a1;a2] -> a1 ^ ".less_equal(" ^ a2 ^ ")"
    | "pvt_float_lt", [a1;a2] -> a1 ^ ".less_than(" ^ a2 ^ ")"
    | "pvt_float_eq", [a1;a2] -> a1 ^ ".equal(" ^ a2 ^ ")"
    | "pvt_float_ne", [a1;a2] -> "!" ^ a1 ^ ".equal(" ^ a2 ^ ")"
    | "pvt_float_neg", [a1] -> "- " ^ a1

    | "pub_float_add", [a1;a2] -> a1 ^ " + " ^ a2
    | "pub_float_sub", [a1;a2] -> a1 ^ " - " ^ a2
    | "pub_float_mul", [a1;a2] -> a1 ^ " * " ^ a2
    | "pub_float_div", [a1;a2] -> a1 ^ " / " ^ a2
    | "pub_float_ge", [a1;a2] -> a1 ^ " >= " ^ a2
    | "pub_float_gt", [a1;a2] -> a1 ^ " > " ^ a2
    | "pub_float_le", [a1;a2] -> a1 ^ " <= " ^ a2
    | "pub_float_lt", [a1;a2] -> a1 ^ " < " ^ a2
    | "pub_float_eq", [a1;a2] -> a1 ^ " == " ^ a2
    | "pub_float_ne", [a1;a2] -> a1 ^ " != " ^ a2
    | "pub_float_neg", [a1] -> "- " ^ a1

    | "plc_float_add", [a1;a2] -> a1 ^ " + " ^ a2
    | "plc_float_sub", [a1;a2] -> a1 ^ " - " ^ a2
    | "plc_float_mul", [a1;a2] -> a1 ^ " * " ^ a2
    | "plc_float_div", [a1;a2] -> a1 ^ " / " ^ a2
    | "plc_float_ge", [a1;a2] -> a1 ^ " >= " ^ a2
    | "plc_float_gt", [a1;a2] -> a1 ^ " > " ^ a2
    | "plc_float_le", [a1;a2] -> a1 ^ " <= " ^ a2
    | "plc_float_lt", [a1;a2] -> a1 ^ " < " ^ a2
    | "plc_float_eq", [a1;a2] -> a1 ^ " == " ^ a2
    | "plc_float_ne", [a1;a2] -> a1 ^ " != " ^ a2
    | "plc_float_neg", [a1] -> "- " ^ a1

    (* bool *)
    | "pvt_bool_and", [a1;a2] -> a1 ^ " & " ^ a2
    | "pvt_bool_or", [a1;a2] -> a1 ^ " | " ^ a2
    | "pvt_bool_eq", [a1;a2] -> a1 ^ " == " ^ a2
    | "pvt_bool_ne", [a1;a2] -> a1 ^ " != " ^ a2
    | "pvt_bool_not", [a1] -> "! " ^ a1

    | "pub_bool_and", [a1;a2] -> a1 ^ " && " ^ a2
    | "pub_bool_or", [a1;a2] -> a1 ^ " || " ^ a2
    | "pub_bool_eq", [a1;a2] -> a1 ^ " == " ^ a2
    | "pub_bool_ne", [a1;a2] -> a1 ^ " != " ^ a2
    | "pub_bool_not", [a1] -> "! " ^ a1

    | "plc_bool_and", [a1;a2] -> a1 ^ " && " ^ a2
    | "plc_bool_or", [a1;a2] -> a1 ^ " || " ^ a2
    | "plc_bool_eq", [a1;a2] -> a1 ^ " == " ^ a2
    | "plc_bool_ne", [a1;a2] -> a1 ^ " != " ^ a2
    | "plc_bool_not", [a1] -> "! " ^ a1

    (* math functions *)
    | "pvt_ceil", [_] -> raise (UnsupportedBuiltin f)
    | "pvt_floor", [_] -> raise (UnsupportedBuiltin f)
    | "pvt_round", [_] -> raise (UnsupportedBuiltin f)
    | "pvt_cos", [a1] -> a1 ^ ".cos()"
    | "pvt_sin", [a1] -> a1 ^ ".sin()"
    | "pvt_tan", [a1] -> Printf.sprintf "(%s.sin() / %s.cos())" a1 a1
    | "pvt_log", [a1] -> a1 ^ ".ln()"
    | "pvt_exp", [a1] -> a1 ^ ".exp()"

    | "pub_ceil", [a1] -> Printf.sprintf "int(ceil%s)" a1
    | "pub_floor", [a1] -> "int" ^ a1
    | "pub_round", [a1] -> Printf.sprintf "int(round%s)" a1
    | "pub_cos", [a1] -> "cos" ^ a1
    | "pub_sin", [a1] -> "sin" ^ a1
    | "pub_tan", [a1] -> "tan" ^ a1
    | "pub_log", [a1] -> "log" ^ a1
    | "pub_exp", [a1] -> "exp" ^ a1

    | "plc_ceil", [a1] -> Printf.sprintf "int(ceil%s)" a1
    | "plc_floor", [a1] -> "int" ^ a1
    | "plc_round", [a1] -> Printf.sprintf "int(round%s)" a1
    | "plc_cos", [a1] -> "cos" ^ a1
    | "plc_sin", [a1] -> "sin" ^ a1
    | "plc_tan", [a1] -> "tan" ^ a1
    | "plc_log", [a1] -> "log" ^ a1
    | "plc_exp", [a1] -> "exp" ^ a1

    (* util *)
    | "pub_int_print", [a1]
    | "plc_int_print", [a1] -> "printf(\"%d\\n\", "^a1^")"
    | "pub_float_print", [a1]
    | "plc_float_print", [a1] -> "printf(\"%f\\n\", "^a1^")"
    | "pub_bool_print", [a1]
    | "plc_bool_print", [a1] -> "printf(\"%d\\n\", "^a1^")"

    | "pub_int_debug1", [_] -> ""
    | "plc_int_debug1", [_] -> ""
    | "pub_bool_debug1", [_] -> ""
    | "plc_bool_debug1", [_] -> ""
    | "pub_float_debug1", [_] -> ""
    | "plc_float_debug1", [_] -> ""

    | _, _ -> raise (UnsupportedBuiltin f)

let rec emp_of_sexpr party se =
  match se.sexpr with
  | SEunit -> raise (FatalInGen "Can not convert SEunit")
  | SEbool b -> string_of_bool b
  | SEnull -> "nullptr"
  | SEint n -> string_of_int n
  | SEfloat f -> Printf.sprintf "%f" f
  | SEref lv -> "& (" ^ emp_of_lvalue lv ^ ")"
  | SEarrayinit (Public _, se_inits)
  | SEarrayinit (Plocal _, se_inits) ->
    let inits = List.map (emp_of_sexpr party) se_inits in
    let text_inits = "{ {" ^ String.concat ", " inits ^ "} }" in
    Printf.sprintf "std::make_unique<%s>(%s %s)" (emp_of_raw_typ (type_of_sexpr se)) (emp_of_raw_typ (type_of_sexpr se)) text_inits
  | SEarrayinit (Private _, _) ->
    raise TODOGen
  | SEstructinit se_asgns ->
    let asgns = List.map (fun (_, se_asgn) -> emp_of_sexpr party se_asgn) se_asgns in
    "{" ^ String.concat ", " asgns ^ "}"
  | SEbuiltin (f, args) -> emp_of_builtin party f (List.map (fun arg -> "(" ^ emp_of_sexpr party arg ^ ")") args)
  | SElexpr sle -> emp_of_slexpr party sle
and emp_of_slexpr party sle =
  match sle.slexpr with
  | SEvar alias -> emp_lname_of_alias alias
  | SEindex (arr, _, index) -> Printf.sprintf "(*(%s))[%s]" (emp_of_slexpr party arr) (emp_of_sexpr party index)
  | SEfield (st, field) -> emp_of_slexpr party st ^ "." ^ field

let rec emp_of_expr party e =
  match e.expr with
  | Eunit -> raise (FatalInGen "Can not convert Eunit")
  | Ebool b -> string_of_bool b
  | Enull -> "nullptr"
  | Eint n -> string_of_int n
  | Efloat f -> Printf.sprintf "%f" f
  | Elexpr le -> emp_of_lexpr party le
  | Eref le -> "& (" ^ emp_of_lexpr party le ^ ")"
  | Earrayinit (Public _, e_inits)
  | Earrayinit (Plocal _, e_inits) ->
    let inits = List.map (emp_of_expr party) e_inits in
    let text_inits = "{ {" ^ String.concat ", " inits ^ "} }" in
    Printf.sprintf "std::make_unique<%s>(%s %s)" (emp_of_raw_typ (type_of_expr e)) (emp_of_raw_typ (type_of_expr e)) text_inits
  | Earrayinit (Private _, _) -> raise TODOGen
  | Estructinit e_asgns ->
    let asgns = List.map (fun (_, e_asgn) -> emp_of_expr party e_asgn) e_asgns in
    "{" ^ String.concat ", " asgns ^ "}"
  | Ebuiltin (f, args) ->
    emp_of_builtin party f (List.map (fun arg -> "(" ^ emp_of_expr party arg ^ ")") args)
and emp_of_lexpr party le =
  match le.lexpr with
  | Evar (var, true) -> "(*" ^ var ^ ")"
  | Evar (var, false) -> var
  | Eindex (arr, _, index) -> Printf.sprintf "(*(%s))[%s]" (emp_of_lexpr party arr) (emp_of_expr party index)
  | Efield (st, field) -> emp_of_lexpr party st ^ "." ^ field
  | Ederef e -> "(* (" ^ emp_of_expr party e ^ "))"

let is_Earrayinit e =
  match e.expr with
  | Earrayinit _ -> true
  | _ -> false

let is_SEarrayinit se =
  match se.sexpr with
  | SEarrayinit _ -> true
  | _ -> false

let rec indent_emp_of_cmd party su_env ind c =
  match c.cmd with
  | Cskip -> ""
  | Cseq (c1, c2) -> indent_emp_of_cmd party su_env ind c1 ^ "\n" ^ indent_emp_of_cmd party su_env ind c2
  | Cdef (ty, var, e) ->
    begin match ty with
    | Tunit -> (* C++ does not allow void variable *)
      ind ^ emp_of_expr party e ^ ";"
    | _ ->
      ind ^ Printf.sprintf "%s %s = %s;" (emp_of_typ ty) var (emp_of_expr party e)
    end
  | Ccall (ty, anno, var, f, args) ->
    let call_text = f ^ "(" ^ String.concat ", " (List.map (fun arg -> "(" ^ emp_of_expr party arg ^ ")") args) ^ ");" in
    begin match ty, anno with
    | Tunit, SANDBOX PLOCAL1 | Tunit, SANDBOX PLOCAL2 -> ""
    | Tunit, _ ->
      ind ^ call_text
    | _, SANDBOX PLOCAL1 | _, SANDBOX PLOCAL2 ->
      if party = PROVER then
        ind ^ Printf.sprintf "%s %s = %s;" (emp_of_typ ty) var call_text
      else
        ind ^ Printf.sprintf "%s %s = %s;" (emp_of_typ ty) var (emp_default_value su_env ty)
    | _, _ ->
      ind ^ Printf.sprintf "%s %s = %s;" (emp_of_typ ty) var call_text
    end
  | Casgn (le, e) -> ind ^ emp_of_lexpr party le ^ " = " ^ emp_of_expr party e ^ ";"
  | Cif (e, c1, c2) ->
    let c1_text = indent_emp_of_cmd party su_env ind c1 in
    let c2_text = indent_emp_of_cmd party su_env ind c2 in
    ind ^ "if (" ^ emp_of_expr party e ^ ")\n" ^ c1_text ^ "\n" ^ ind ^ "else\n" ^ c2_text
  | Cwhile (e, c) -> ind ^ "while ("^ emp_of_expr party e ^ ")\n" ^ indent_emp_of_cmd party su_env ind c
  | Csection c -> ind ^ "{\n" ^ indent_emp_of_cmd party su_env (ind^"  ") c ^ "\n" ^ ind ^ "}"
  | Creturn e ->
    let ret_text = match e.expr with
    | Eunit -> ""
    | _ -> " " ^ emp_of_expr party e ^ ""
    in
    ind ^ "return" ^ ret_text ^ ";"
  | Cbreak -> ind ^ "break;"
  | Ccontinue -> ind ^ "continue;"
  | Cassert e ->
    match type_of_expr e with
    | Tbool (Public _) -> ind ^ Printf.sprintf "assert(%s);" (emp_of_expr party e)
    | Tbool (Private _) -> ind ^ Printf.sprintf "assert((%s).reveal<bool>(PUBLIC));" (emp_of_expr party e)
    | Tbool (Plocal _) -> ind ^ Printf.sprintf "assert(%s);" (emp_of_expr party e)
    | _ -> raise (FatalInAST "Assertion does not have boolean type")

let rec type_has_array su_env = function
| Tunit | Tint _ | Tfloat _ | Tbool _ -> false
| Tref _ -> false
| Tarray _ -> true
| Tstruct st_name ->
  let st = find_struct su_env st_name in
  List.exists (fun (ty_elem, _) -> type_has_array su_env ty_elem) st.struct_fields

let output_init_context oc su_env vars noc =
  output_string oc "OUContext::OUContext() {\n";
  (* allocate all arrays inside name if there's any *)
  let rec output_var_init name ty =
    match ty with
    | Tunit | Tint _ | Tfloat _ | Tbool _ | Tref _ -> ()
    | Tarray (ty_elem, Public _, size)
    | Tarray (ty_elem, Plocal _, size) ->
      (* allocate top-level array *)
      Printf.fprintf oc "  %s = make_unique<%s>();\n" name (emp_of_raw_typ ty);
      (* allocate arrays inside each index *)
      if type_has_array su_env ty_elem then begin
        Printf.fprintf oc "  for (int i = 0; i < %d; i++) {\n" size;
        let elem_text = Printf.sprintf "(*%s)[i]" name in
        output_var_init elem_text ty_elem;
        Printf.fprintf oc "  }\n"
      end
    | Tarray (_, Private _, _) -> raise TODOGen
    | Tstruct st_name ->
      let st = find_struct su_env st_name in
      (* allocate arrays inside each field *)
      List.iter (fun (ty_field, field) ->
        output_var_init (name ^ "." ^ field) ty_field
      ) st.struct_fields
  in
  Seq.iter (fun (alias, ty) ->
    output_var_init (emp_name_of_alias alias) ty
  ) vars;
  (* init digests *)
  Printf.fprintf oc "  OUdepend_edges = new vector<HashEdge>[%d];\n" noc;
  Printf.fprintf oc "  OUproduce_edges = new vector<HashEdge>[%d];\n" noc;
  output_string oc "}\n"

let output_decl_context oc vars =
  output_string oc "
struct HashEdge {
  int src_id;
  int dst_id;
  char* dgst;
};\n";
  output_string oc "struct OUContext {\n";
  output_string oc "  OUContext();\n";
  Printf.fprintf oc "  vector<HashEdge>* OUdepend_edges;\n";
  Printf.fprintf oc "  vector<HashEdge>* OUproduce_edges;\n";
  Seq.iter (fun (alias, ty) ->
    match ty with
    | Tunit -> ()
    | _ -> Printf.fprintf oc "  %s %s;\n" (emp_of_typ ty) (emp_name_of_alias alias)
  ) vars;
  output_string oc "};\n"

let output_decl_produces oc frag =
  let output_decl_produce node =
    if List.length node.cmdinfo_defs > 0 then
      Printf.fprintf oc "void produce_%d(OUContext *);\n" node.cmdinfo_id
  in
  Seq.iter output_decl_produce frag

let output_decl_syncs oc frag =
  let output_decl_sync node =
    if List.length node.cmdinfo_deps > 0 then
      Printf.fprintf oc "void sync_%d(OUContext *);\n" node.cmdinfo_id
  in
  Seq.iter output_decl_sync frag

let add_rawdata_lvalue indent data lv =
  match type_of_lvalue lv with
  | Tunit -> raise (FatalInGen "Can not generate TVunit")
  | Tint (Public _) | Tint (Plocal _)
  | Tfloat (Public _) | Tfloat (Plocal _)
  | Tbool (Public _) | Tbool (Plocal _) ->
    "" (* TODO: should add them *)
  | Tint (Private _) -> indent ^ Printf.sprintf "OU_add_int(%s, %s);" data (emp_of_lvalue lv)
  | Tfloat (Private _) -> indent ^ Printf.sprintf "OU_add_Float(%s, %s);" data (emp_of_lvalue lv)
  | Tbool (Private _) -> indent ^ Printf.sprintf "OU_add_bit(%s, %s);" data (emp_of_lvalue lv)
  | _ -> raise (FatalInGen "TODO")

let output_def_produces _ oc frag =
  let output_produce node =
    Printf.fprintf oc "void produce_%d(OUContext *ctx) {\n" node.cmdinfo_id;
    List.iter (fun (dst_id, dst_seg_id, lvs) ->
      Printf.fprintf oc " // used by command %d in segment %d\n" dst_id dst_seg_id;
      output_string oc "  {
    vector<block> *OUdata = new vector<block>{};
    auto hash_start_time = high_resolution_clock::now();\n";
      List.iter (fun lv ->
        output_string oc (add_rawdata_lvalue "    " "*OUdata" lv ^ "\n")
      ) lvs;
      Printf.fprintf oc "    char* OUdgst = OUget_digest(*OUdata);
    delete OUdata;
    ctx->OUproduce_edges[%d].push_back({%d, %d, OUdgst});\n" dst_seg_id node.cmdinfo_id dst_id;
    output_string oc "    consistency_cost += high_resolution_clock::now() - hash_start_time;\n";
    output_string oc "  }\n"
    ) node.cmdinfo_defs;
    output_string oc "}\n\n"
  in
  Seq.iter (fun node ->
    if List.length node.cmdinfo_defs > 0 then
      output_produce node
  ) frag

let output_def_syncs party oc deps frag =
  let output_sync dep node =
    Printf.fprintf oc "void sync_%d(OUContext *ctx) {\n" node.cmdinfo_id;
    output_string oc "auto sync_start_time = high_resolution_clock::now();\n";
    (* update lvalues *)
    LValueHashtbl.iter (fun lv tv ->
      Printf.fprintf oc "  %s = %s;\n" (emp_of_lvalue lv) (emp_of_typed_value party tv)
    ) dep;
    output_string oc "sync_cost += high_resolution_clock::now() - sync_start_time;\n";
    (* update hash *)
    List.iter (fun (src_id, src_seg_id, lvs) ->
      Printf.fprintf oc "  // coming from command %d in segment %d\n" src_id src_seg_id;
      output_string oc "  {
    vector<block> *OUdata = new vector<block>{};
    auto hash_start_time = high_resolution_clock::now();\n";
      List.iter (fun lv ->
        output_string oc (add_rawdata_lvalue "    " "*OUdata" lv ^ "\n")
      ) lvs;
      Printf.fprintf oc "    char* OUdgst = OUget_digest(*OUdata);
    delete OUdata;
    ctx->OUdepend_edges[%d].push_back({%d, %d, OUdgst});\n" src_seg_id src_id node.cmdinfo_id;
    output_string oc "    consistency_cost += high_resolution_clock::now() - hash_start_time;\n";
    output_string oc "  }\n"
    ) node.cmdinfo_deps;
    Printf.fprintf oc "}\n\n"
  in
  Seq.iter2 (fun dep node ->
    if LValueHashtbl.length dep > 0 then
      output_sync dep node
  ) deps frag

let output_def_consistency_check _ oc noc =
  Printf.fprintf oc "#define OU_NOC %d\n" noc;
  output_string oc "
void merge_digests(vector<HashEdge>& edges, char* dgst) {
  Hash h;
  for (auto edge : edges) {
    h.put(edge.dgst, emp::Hash::DIGEST_SIZE);
  }
  h.digest(dgst);
}

void debug_digest(char* dgst) {
  for (int i = 0; i < emp::Hash::DIGEST_SIZE; i++) {
    printf(\"%x\", dgst[i]);
  }
  printf(\"\\n\");
}

void consistency_check(OUContext *ctx) {
  auto hash_start_time = high_resolution_clock::now();
  for (int t = 0; t < OU_NOC; t++) {
    if (!ctx->OUproduce_edges[t].empty()) {
      sort(ctx->OUproduce_edges[t].begin(), ctx->OUproduce_edges[t].end());
      char dgst[emp::Hash::DIGEST_SIZE];
      merge_digests(ctx->OUproduce_edges[t], dgst);
      printf(\"produce to %d:\\t\", t);
      debug_digest(dgst);
    }
    if (!ctx->OUdepend_edges[t].empty()) {
      sort(ctx->OUdepend_edges[t].begin(), ctx->OUdepend_edges[t].end());
      char dgst[emp::Hash::DIGEST_SIZE];
      merge_digests(ctx->OUdepend_edges[t], dgst);
      printf(\"depend on %d:\\t\", t);
      debug_digest(dgst);
    }
  }
  auto end_time = high_resolution_clock::now();
  consistency_cost += high_resolution_clock::now() - hash_start_time;
  printf(\"consistency check cost: %.8lfs\\n\", consistency_cost.count());
  printf(\"sync cost: %.8lfs\\n\", sync_cost.count());
}
"

let output_ou_main party oc su_env frag =
  let output_scmd sc =
    match sc.scmd with
    | SCdef (ty, alias, se) ->
      begin match ty with
      | Tunit -> (* C++ does not allow void variable *)
        Printf.fprintf oc "  %s;\n" (emp_of_sexpr party se)
      | _ ->
        Printf.fprintf oc "  ctx->%s = %s;\n" (emp_name_of_alias alias) (emp_of_sexpr party se)
      end
    | SCasgn (sle, se) ->
      Printf.fprintf oc "  %s = %s;\n" (emp_of_slexpr party sle) (emp_of_sexpr party se)
    | SCassert se ->
      begin match type_of_sexpr se with
      | Tbool (Private _) -> Printf.fprintf oc "  assert((%s).reveal<bool>());\n" (emp_of_sexpr party se)
      | Tbool (Public _)
      | Tbool (Plocal _) -> Printf.fprintf oc "  assert(%s);\n" (emp_of_sexpr party se)
      | _ -> raise (FatalInGen "assertion does not have boolean type")
      end
    | SCcall (ty, alias, f, args, pubR) ->
      (* sync *)
      List.iter (fun (lv, v) ->
        Printf.fprintf oc "  %s = %s;\n" (emp_of_lvalue lv) (emp_of_value v)) pubR;
      (* receiver *)
      begin match ty with
      | Tunit -> output_string oc "  "
      | _ -> Printf.fprintf oc "  %s =" (emp_lname_of_alias alias)
      end;
      Printf.fprintf oc "%s(%s);\n" f (String.concat ", " (List.map (fun arg -> emp_of_sexpr party arg) args))
    | SCsandboxcall (ty, kind, alias, f, args) ->
      (* prepare type and variable *)
      begin match ty with
      | Tunit -> output_string oc "  "
      | _ -> Printf.fprintf oc "  %s =" (emp_lname_of_alias alias)
      end;
      (* rhs *)
      begin match kind with
      | BLACKBOX1 | BLACKBOX2 ->
        Printf.fprintf oc "%s(%s);\n" f (String.concat ", " (List.map (fun arg -> emp_of_sexpr party arg) args))
      | PLOCAL1 | PLOCAL2 ->
        if party = PROVER then
          Printf.fprintf oc "%s(%s);\n" f (String.concat ", " (List.map (fun arg -> emp_of_sexpr party arg) args))
        else
          Printf.fprintf oc "%s;\n" (emp_default_value su_env ty)
      end
  in
  output_string oc "void OU_main() {\n";
  output_string oc "  OUContext *ctx = new OUContext();\n";
  (*
  (* define global variables *)
  List.iter (fun gvar_node ->
    let gvar_def = gvar_node.gvardef in
    let ty = gvar_def.gvar_typ in
    let name = gvar_def.gvar_name in
    Printf.fprintf oc "  %s %s_impl;\n" (emp_of_typ ty) name;
    Printf.fprintf oc "  %s = & %s_impl;\n" name name
    ) gvars;
  (* output dependent variables, skip global variables *)
  Seq.iter (fun (alias, ty) ->
    if is_global_alias alias then begin
      (*
      let name = emp_name_of_alias alias in
      Printf.fprintf oc "  %s %s_impl;\n" (emp_of_typ ty) name;
      Printf.fprintf oc "  %s = & %s_impl;\n" name name
      *)
    end
    else
      Printf.fprintf oc "  %s %s = %s;\n" (emp_of_typ ty) (emp_lname_of_alias alias) (emp_default_value su_env ty)
    ) dep_vars;
  *)
  (*
  (* update live-in *)
  output_string oc "// OU_LIVEIN_START\n";
  LValueTree.iter su_env (fun lv ->
    let ty = type_of_lvalue lv in
    Printf.fprintf oc "  %s = %s;\n"
    (emp_of_lvalue lv)
    (emp_default_value su_env ty)) live_in;
  output_string oc "// OU_LIVEIN_END\n";
  *)
  (* output commands *)
  Seq.iter (fun node ->
    if List.length node.cmdinfo_deps > 0 then begin
      Printf.fprintf oc "  sync_%d(ctx);\n" node.cmdinfo_id
    end;
    output_scmd node.cmdinfo_cmd;
    if List.length node.cmdinfo_defs > 0 then begin
      Printf.fprintf oc "  produce_%d(ctx);\n" node.cmdinfo_id
    end
  ) frag;
  output_string oc "  consistency_check(ctx);\n";
  output_string oc "}\n"

let output_headers oc ~with_ou_funs =
  output_string oc "
#include \"emp-tool/emp-tool.h\"
#include \"emp-zk/emp-zk.h\"
#include <iostream>
#include <math.h>

using namespace emp;
using namespace std;\n";
  if with_ou_funs then output_string oc "
int OU_verifier_rand(int, int);
int OU_prover_rand(int, int);\n\n"

let output_cpp_main oc =
  output_string oc "
const int threads = 1;
BoolIO<NetIO>* EMP_ios[threads];

int main(int argc, char** argv) {
  int port = argc > 1 ? atoi(argv[1]) : 12345;
  for(int i = 0; i < threads; ++i) {
    EMP_ios[i] = new BoolIO<NetIO>(new NetIO(party == ALICE?nullptr:\"127.0.0.1\",port+i), party==ALICE);
  }

  setup_zk_bool<BoolIO<NetIO>>(EMP_ios, threads, party);

  printf(\"start\\n\");
  OU_main();

  bool cheat = finalize_zk_bool<BoolIO<NetIO>>();
	if(cheat) error(\"cheat!\\n\");
  else printf(\"success!\\n\");

  for(int i = 0; i < threads; ++i) {
    delete EMP_ios[i]->io;
    delete EMP_ios[i];
  }
  return 0;
}"

let collect_vars prog =
  let var_types = AliasHashtbl.create 10 in
  let record_var_type ty alias =
    if not (AliasHashtbl.mem var_types alias) then
      AliasHashtbl.add var_types alias ty
  in
  let collect_dep_var node =
    List.iter (fun (_, _, deps) ->
      List.iter (fun lv ->
        let ty, alias = base_of_lvalue lv in
        record_var_type ty alias
      ) deps
    ) node.cmdinfo_deps
  in
  let collect_def_var node =
    match node.cmdinfo_cmd.scmd with
    | SCdef (ty, alias, _) -> record_var_type ty alias
    | SCcall (ty, alias, _, _, _) -> record_var_type ty alias
    | SCasgn (sle, _) ->
      let ty, alias = base_of_slexpr_node sle in
      record_var_type ty alias
    | _ -> ()
  in
  let collect_sync_var node =
    match node.cmdinfo_cmd.scmd with
    | SCcall (_, _, _, _, pubR) ->
      List.iter (fun (lv, _) ->
        let ty, alias = base_of_lvalue lv in
        record_var_type ty alias) pubR
    | _ -> ()
  in
  Seq.iter (fun node ->
    collect_dep_var node;
    collect_def_var node;
    collect_sync_var node
  ) prog;
  AliasHashtbl.to_seq var_types

(** Collect all variables appearing in live_in, and all variables appearing in sync but not defined in prog *)
let collect_dep_vars prog =
  let var_types = AliasHashtbl.create 10 in
  let record_var_type ty alias =
    if not (AliasHashtbl.mem var_types alias) then
      AliasHashtbl.add var_types alias ty
  in
  let rec var_of_lvalue lv =
    match lv.lvalue with
    | Vvar alias -> type_of_lvalue lv, alias
    | Vindex (lv, _, _) -> var_of_lvalue lv
    | Vfield (lv, _) -> var_of_lvalue lv
  in
  let collect_livein_vars prog =
    Seq.iter (fun node ->
      List.iter (fun (_, _, deps) ->
        List.iter (fun lv ->
          let ty, alias = var_of_lvalue lv in
          record_var_type ty alias
        ) deps
      ) node.cmdinfo_deps
    ) prog
  in
  let collect_sync_vars prog =
    Seq.iter (fun node ->
      match node.cmdinfo_cmd.scmd with
      | SCcall (_, _, _, _, pubR) ->
        List.iter (fun (lv, _) ->
          let ty, alias = var_of_lvalue lv in
          record_var_type ty alias) pubR
      | _ -> ()
    ) prog
  in
  let all_def_vars prog =
    Seq.fold_left (fun set node ->
      match node.cmdinfo_cmd.scmd with
      | SCdef (_, alias, _) -> AliasSet.add alias set
      | SCcall (_, alias, _, _, _) -> AliasSet.add alias set
      | _ -> set
    ) AliasSet.empty prog
  in
  collect_livein_vars prog;
  collect_sync_vars prog;
  let def_vars = all_def_vars prog in
  (* generate livein_vars + sync_vars - def_vars *)
  AliasSet.iter (fun alias ->
    AliasHashtbl.remove var_types alias
  ) def_vars;
  AliasHashtbl.to_seq var_types

let output_struct_def oc st =
  output_string oc ("struct " ^ st.struct_name ^ " { \n");
  List.iter (fun (ty, field_name) -> output_string oc (" " ^ emp_of_typ ty ^ " " ^ field_name ^ ";\n")) st.struct_fields;
  output_string oc "};\n\n"
(*
let output_gvar_def oc ty alias =
  if is_global_alias alias then
    Printf.fprintf oc "%s * %s;" (emp_of_typ ty) (emp_lname_of_alias alias)
  else
    Printf.fprintf oc "%s %s;" (emp_of_typ ty) (emp_lname_of_alias alias)
*)
(* TODO: consider plocal *)
let output_fundef party oc su_env fd =
  Printf.fprintf oc "%s %s(%s) {\n"
    (emp_of_typ fd.fun_ret_typ) fd.fun_name
    (String.concat ", " (List.map (fun (ty, param_name) ->
      emp_of_param_typ ty ^ " " ^ param_name) fd.fun_params));
  begin
    if party = VERIFIER && fd.fun_anno = SANDBOX PLOCAL1 then (* return a place holder because we will never use this value *)
      match fd.fun_ret_typ with
      | Tunit -> output_string oc "  return;\n"
      | ty -> Printf.fprintf oc "  %s result;\n  return result;\n" (emp_of_typ ty)
    else
      Printf.fprintf oc "%s\n" (indent_emp_of_cmd party su_env "  " fd.fun_body)
  end;
  output_string oc "}\n\n"

let output_fundecl oc fx =
  Printf.fprintf oc "%s %s(%s);\n"
    (emp_of_typ fx.pxfun_ret_typ) fx.pxfun_name
    (String.concat ", " (List.map (fun (ty, _) ->
      emp_of_param_typ ty) fx.pxfun_params))

let output_emp_head party headname su_env fds fxs gvars =
  let oc = open_out headname in
  (* output headers *)
  output_string oc "#pragma once\n\n";
  output_headers oc ~with_ou_funs:true;
  let party_code = if party = PROVER then "ALICE" else "BOB" in
  output_string oc ("#define party " ^ party_code ^ "\n\n");
  (* output struct definitions *)
  Hashtbl.iter (fun _ st -> output_struct_def oc st) su_env.su_structs;
  (* output declarations of global variables' pointers *)
  List.iter (fun gvar_node ->
    let gvar = gvar_node.gvardef in
    Printf.fprintf oc "extern %s * %s;\n"
      (emp_of_typ gvar.gvar_typ)
      gvar.gvar_name) gvars;
  (* output functions declarations *)
  List.iter (fun fd_node ->
    let fd = fd_node.fundef in
    if fd.fun_name <> "main" then
    (* if fd.fun_anno = ATOMIC || fd.fun_anno = PLOCAL1 then *)
      Printf.fprintf oc "%s %s(%s);\n"
        (emp_of_typ fd.fun_ret_typ) fd.fun_name
        (String.concat ", " (List.map (fun (ty, _) ->
          emp_of_param_typ ty) fd.fun_params))
    ) fds;
  List.iter (fun fx ->
    match fx.pxfun_anno with
    | SANDBOX PLOCAL1 | SANDBOX PLOCAL2 ->
      if party = PROVER then output_fundecl oc fx
    | SANDBOX BLACKBOX1 | SANDBOX BLACKBOX2 ->
      output_fundecl oc fx
    | _ -> raise (FatalInGen "Unknown anno type in external function declaration")
    ) fxs;
  close_out oc

let output_emp_defs party filename su_env gvars fds =
  let oc = open_out filename in
  (* output headers *)
  Printf.fprintf oc "#include \"common.h\"\n\n";
  (* output builtin functions *)
  output_string oc "
extern BoolIO<NetIO>* EMP_ios[1];
int OU_verifier_rand(int a, int b) {
  int r = 0;
  if (party == BOB) {
    PRG prg;
    std::uniform_int_distribution<> distrib(a, b);
    r = distrib(prg);
    EMP_ios[0]->send_data(&r, sizeof(r));
  }
  else {
    EMP_ios[0]->recv_data(&r, sizeof(r));
  }
  return r;
}

int OU_prover_rand(int a, int b) {
  if (party == ALICE) {
    PRG prg;
    std::uniform_int_distribution<> distrib(a, b);
    return distrib(prg);
  }
  else return 0;
}

";
  (* output global variables' pointers *)
  List.iter (fun gvar_node ->
    let gvar = gvar_node.gvardef in
    Printf.fprintf oc "%s * %s;\n"
    (emp_of_typ gvar.gvar_typ)
    gvar.gvar_name) gvars;
  output_char oc '\n';
  (* output function definitions *)
  List.iter (fun fd_node ->
    let fd = fd_node.fundef in
    if fd.fun_name <> "main" then output_fundef party oc su_env fd) fds;
  close_out oc

let output_emp party filename su_env (*gvars*)_ frag noc =
  let vars = collect_vars frag in
  let oc = open_out filename in
  (* output headers *)
  Printf.fprintf oc "#include \"common.h\"\n\n";
  output_decl_context oc vars;
  output_string oc "\n";
  output_init_context oc su_env vars noc;
  output_decl_produces oc frag;
  output_decl_syncs oc frag;
  output_string oc "void consistency_check(OUContext *);\n";
  output_string oc "\n";
  (* output protocol fragment *)
  output_ou_main party oc su_env frag;
  (* output the C++ main function *)
  output_cpp_main oc;
  close_out oc

let output_emp_sync party filename deps frag noc =
  let vars = collect_vars frag in
  let oc = open_out filename in
  output_string oc "#pragma once\n\n";
  output_headers oc ~with_ou_funs:false;
  output_string oc "\n";
  output_decl_context oc vars;
  (* output_decl_vars oc vars; *)
  output_string oc "\n";
  output_string oc "
#include <chrono>
using namespace std::chrono;

duration<float> consistency_cost(0);
duration<float> sync_cost(0);

bool operator<(const HashEdge &lhs, const HashEdge &rhs) {
  return lhs.src_id < rhs.src_id || (lhs.src_id == rhs.src_id && lhs.dst_id < rhs.dst_id);
}

void Ou_add_bit(vector<block> &data, const Bit &x) {
  data.push_back(x.bit);
}

void Ou_add_int(vector<block> &data, const Integer &x) {
  for(size_t i = 0; i < x.size(); ++i)
    data.push_back(x[i].bit);
}

void OU_add_Float(vector<block> &data, const Float &x) {
  for (size_t i = 8; i < 32; ++i) // ignore the last few bits of fraction
    data.push_back((block)x[i].bit);
}

char* OUget_digest(vector<block> &data) {
  bool* res = new bool[data.size()];
  ((ZKBoolCircExec<BoolIO<NetIO>>*)(CircuitExecution::circ_exec))->ostriple->verify_output(res, data.data(), data.size());
		for(int i = 0; i < ((ZKBoolCircExec<BoolIO<NetIO>>*)(CircuitExecution::circ_exec))->ostriple->threads; ++i)
			((ZKBoolCircExec<BoolIO<NetIO>>*)(CircuitExecution::circ_exec))->ostriple->ios[i]->flush();
  Hash h;
  h.put(res, data.size());
  delete res;
  char* dgst = new char[emp::Hash::DIGEST_SIZE];
  h.digest(dgst);
  return dgst;
}
\n";
  output_def_produces party oc frag;
  output_def_syncs party oc deps frag;
  output_def_consistency_check party oc noc;
  close_out oc

let output_emp_depend party filename su_env fds =
  let oc = open_out filename in
  Printf.fprintf oc "#include \"common.h\"\n";
  (* output function definitions *)
  List.iter (fun fd_node ->
    let fd = fd_node.fundef in
    match fd.fun_anno with
    | SANDBOX PLOCAL1 | SANDBOX PLOCAL2 ->
      output_fundef party oc su_env fd
    | _ -> ()
    ) fds;
  close_out oc

let output_makefile filename noc =
  let oc = open_out filename in
  (* genrate ["part0 part1"; ... ] *)
  let parts =
    let rec parts_from idx =
      if idx < noc then
        ("part" ^ string_of_int idx) :: parts_from (idx+1)
      else []
    in parts_from 0
  in
  output_string oc ("
CXX_INCLUDE=-I /usr/local/include/emp-tool -I /usr/local/include/emp-zk
CXX_FLAGS=-msse4.1 -mrdseed -maes -mpclmul -O3 -pthread -w
CXX_O0FLAGS=-msse4.1 -mrdseed -maes -mpclmul -O0 -pthread -w
CXX_LIBS=-lemp-tool -lemp-zk -lgmp -lssl -lcrypto -lgmp
CC=g++

.PHONY: all clean
all: " ^ String.concat " " parts ^ "

.PRECIOUS: %.o part%.o sync%.o

depend.o: depend.cpp common.h
	$(CC) -c -o $@ $< $(CXX_INCLUDE) $(CXX_FLAGS)

common.o: common.cpp common.h
	$(CC) -c -o $@ $< $(CXX_INCLUDE) $(CXX_FLAGS)

part%.o: part%.cpp common.h
	$(CC) -c -o $@ $< $(CXX_INCLUDE) $(CXX_FLAGS)

sync%.o: sync%.cpp
	$(CC) -c -o $@ $< $(CXX_INCLUDE) $(CXX_O0FLAGS)

part%: part%.o sync%.o common.o depend.o
	$(CC) $^ -o $@ $(CXX_LIBS) $(CXX_FLAGS)

clean:
	rm -f *.o " ^ String.concat " " parts ^ "\n")

let emp_of_edge pvt_in =
  String.concat "\n" (List.map (fun (lv, v) ->
    Printf.sprintf "  %s = %s;"
    (emp_of_lvalue lv)
    (emp_of_expr PROVER v)) pvt_in)