open Ast

exception TODOGen
exception UnsupportedBuiltin of string
exception FatalInGen of string
exception UnsupportedType of string
exception UnsupportedCmd of string

(** This is used when refering to a variable as an lvalue. *)
let zokrates_lname_of_alias = function
  | AliasNorm (var, n) -> Printf.sprintf "%s_%d" var n
  | AliasGlob var -> var

(** This is used when defining a variable of this alias. *)
let zokrates_name_of_alias = function
| AliasNorm (var, n) -> var ^ "_" ^ string_of_int n
| AliasGlob var -> var

(** The type that has unique_ptr<...> *)
let rec zokrates_of_typ = function
  | Tarray (ty, Public _, size)
  | Tarray (ty, Plocal _, size) -> Printf.sprintf "%s[%d]" (zokrates_of_typ ty) size
  | Tarray (ty, Private _, size) -> Printf.sprintf "%s[%d]" (zokrates_of_typ ty) size
  | ty -> zokrates_of_raw_typ ty

(** The type used in unique_ptr<...> *)
and zokrates_of_raw_typ = function
  | Tunit -> ""
  | Tbool (Private _) -> "bool"
  | Tbool (Public _) -> "bool"
  | Tbool (Plocal _) -> "bool"
  | Tint (Private _) -> "u32"
  | Tint (Public _) -> "u32"
  | Tint (Plocal _) -> "u32"
  | Tfloat (Private _) -> raise (UnsupportedType "float")
  | Tfloat (Public _) -> raise (UnsupportedType "float")
  | Tfloat (Plocal _) -> raise (UnsupportedType "float")
  | Tarray (ty, Public _, size)
  | Tarray (ty, Plocal _, size) -> Printf.sprintf "%s[%d]" (zokrates_of_typ ty) size
  | Tarray (_, Private _, _ ) -> raise TODOGen
  | Tstruct st_name -> st_name
  | Tref _ -> raise (UnsupportedType "pointer")

let zokrates_of_param_typ = function
  | Tarray (_, Public _, _)
  | Tarray (_, Plocal _, _) -> raise TODOGen
  | Tarray (_, Private _, _ ) -> raise TODOGen
  | ty -> zokrates_of_typ ty

let rec zokrates_of_value = function
  | Vunit -> raise (FatalInGen "can not define Vunit in zokrates")
  | Vint i -> string_of_int i
  | Vfloat _ -> raise (UnsupportedType "float")
  | Vbool b -> string_of_bool b
  | Vref lv -> "& (" ^ zokrates_of_lvalue lv ^ ")"
  | Vnull -> "nullptr"
  | Varray _ -> raise (FatalInGen "can not define Varray in zokrates")
  | Vstruct st ->
    let asgns = Hashtbl.fold (fun _ v asgns' -> (zokrates_of_value v) :: asgns') st [] in
    "{" ^ String.concat ", " asgns ^ "}"
and zokrates_of_lvalue lv =
  match lv.lvalue with
  | Vvar var -> zokrates_lname_of_alias var
  | Vindex (arr, _, index) -> Printf.sprintf "(%s)[%s]" (zokrates_of_lvalue arr) (string_of_int index)
  | Vfield (st, field) -> zokrates_of_lvalue st ^ "." ^ field

let rec zokrates_default_value su_env ty =
  match ty with
  | Tunit -> ""
  | Tbool (Private _) -> "false"
  | Tbool (Public _) -> "false"
  | Tbool (Plocal _) -> "false"
  | Tint (Private _) -> "0"
  | Tint (Public _) -> "0"
  | Tint (Plocal _) -> "0"
  | Tfloat _ -> raise (UnsupportedType "float")
  | Tarray (_, Public _, _)
  | Tarray (_, Plocal _, _) ->
    Printf.sprintf "std::make_unique<%s>()" (zokrates_of_raw_typ ty)
    (*
    let elem_text = zokrates_default_value su_env ty_elem in
    "{" ^ String.concat ", " (list_repeat elem_text size) ^ "}"
    *)
  | Tarray (_, Private _, _) -> raise TODOGen
  | Tstruct st_name ->
    let st = find_struct su_env st_name in
    let asgns = List.map (fun (ty_field, _) -> zokrates_default_value su_env ty_field) st.struct_fields in
    "{" ^ String.concat ", " asgns ^ "}"
  | Tref _ -> raise (UnsupportedType "pointer")

let rec zokrates_of_typed_value tv =
  match tv with
  | TVunit -> raise (FatalInGen "Can not generate TVunit")
  | TVint (_, i) -> string_of_int i
  | TVbool (_, b) -> string_of_bool b
  | TVfloat _ -> raise (UnsupportedType "float")
  | TVref _ -> raise (UnsupportedType "pointer")
  | TVnull -> raise (UnsupportedType "pointer")
  | TVarray (ty_elem, sec, size, arr) ->
    begin match sec with
    | Private _ -> raise (FatalInGen "Can not generate private array")
    | Public _ | Plocal _ ->
      let text_typ = Printf.sprintf "array<%s, %d>" (zokrates_of_typ ty_elem) size in
      let text_inits = String.concat ", " (List.of_seq (Seq.map (fun tv_elem ->
        zokrates_of_typed_value tv_elem
      ) (Array.to_seq arr))) in
      Printf.sprintf "std::make_unique<%s>(%s{%s})" text_typ text_typ text_inits
    end
  | TVstruct map ->
    let asgns = List.of_seq (Seq.map (fun (field, tv_field) ->
      Printf.sprintf ".%s = %s" field (zokrates_of_typed_value tv_field)
    ) (StringMap.to_seq map)) in
    "{" ^ String.concat ", " asgns ^ "}"

let zokrates_of_builtin f args =
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
  | "k2pvt_int_of_pub", [a1] -> a1
  | "k1pvt_float_of_pub", [a1]
  | "k2pvt_float_of_pub", [a1] -> a1
  | "k1pvt_bool_of_pub", [a1]
  | "k2pvt_bool_of_pub", [a1] -> a1

  | "k1pub_int_of_pvt", [a1]
  | "k2pub_int_of_pvt", [a1] -> a1
  | "k1pub_float_of_pvt", [a1]
  | "k2pub_float_of_pvt", [a1] -> a1
  | "k1pub_bool_of_pvt", [a1]
  | "k2pub_bool_of_pvt", [a1] -> a1

  | "k1pvt_int_of_plc", [a1]
  | "k2pvt_int_of_plc", [a1] -> a1
  | "k1pvt_float_of_plc", [a1]
  | "k2pvt_float_of_plc", [a1] -> a1
  | "k1pvt_bool_of_plc", [a1]
  | "k2pvt_bool_of_plc", [a1] -> a1

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
    | "pvt_int_lnot", _ -> raise (UnsupportedBuiltin "lnot")
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
    | "pub_int_lnot", _ -> raise (UnsupportedBuiltin "lnot")
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
    | "plc_int_lnot", _ -> raise (UnsupportedBuiltin "lnot")
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
    | "plc_int_print", [a1] -> "log(\"{}\", "^a1^")"
    | "pub_float_print", [a1]
    | "plc_float_print", [a1] -> "log(\"{}\", "^a1^")"
    | "pub_bool_print", [a1]
    | "plc_bool_print", [a1] -> "log(\"{}\", "^a1^")"

    | "pub_int_debug1", [_] -> ""
    | "plc_int_debug1", [_] -> ""
    | "pub_bool_debug1", [_] -> ""
    | "plc_bool_debug1", [_] -> ""
    | "pub_float_debug1", [_] -> ""
    | "plc_float_debug1", [_] -> ""

    | _, _ -> raise (UnsupportedBuiltin f)

let rec zokrates_of_sexpr se =
  match se.sexpr with
  | SEunit -> raise (FatalInGen "Can not convert SEunit")
  | SEbool b -> string_of_bool b
  | SEnull -> raise (UnsupportedType "pointer")
  | SEint n -> string_of_int n
  | SEfloat _ -> raise (UnsupportedType "float")
  | SEref _ -> raise (UnsupportedType "pointer")
  | SEarrayinit (Public _, se_inits)
  | SEarrayinit (Plocal _, se_inits) ->
    let inits = List.map zokrates_of_sexpr se_inits in
    "[" ^ String.concat ", " inits ^ "]"
  | SEarrayinit (Private _, _) ->
    raise TODOGen
  | SEstructinit se_asgns ->
    let asgns = List.map (fun (_, se_asgn) -> zokrates_of_sexpr se_asgn) se_asgns in
    "{" ^ String.concat ", " asgns ^ "}"
  | SEbuiltin (f, args) -> zokrates_of_builtin f (List.map (fun arg -> "(" ^ zokrates_of_sexpr arg ^ ")") args)
  | SElexpr sle -> zokrates_of_slexpr sle
and zokrates_of_slexpr sle =
  match sle.slexpr with
  | SEvar alias -> zokrates_lname_of_alias alias
  | SEindex (arr, _, index) -> Printf.sprintf "(%s)[%s]" (zokrates_of_slexpr arr) (zokrates_of_sexpr index)
  | SEfield (st, field) -> zokrates_of_slexpr st ^ "." ^ field

let rec zokrates_of_expr e =
  match e.expr with
  | Eunit -> raise (FatalInGen "Can not convert Eunit")
  | Ebool b -> string_of_bool b
  | Enull -> raise (UnsupportedType "pointer")
  | Eint n -> string_of_int n
  | Efloat _ -> raise (UnsupportedType "pointer")
  | Elexpr le -> zokrates_of_lexpr le
  | Eref _ -> raise (UnsupportedType "pointer")
  | Earrayinit (Public _, e_inits)
  | Earrayinit (Plocal _, e_inits) ->
    let inits = List.map zokrates_of_expr e_inits in
    "[" ^ String.concat ", " inits ^ "]"
  | Earrayinit (Private _, _) -> raise TODOGen
  | Estructinit e_asgns ->
    let asgns = List.map (fun (_, e_asgn) -> zokrates_of_expr e_asgn) e_asgns in
    "{" ^ String.concat ", " asgns ^ "}"
  | Ebuiltin (f, args) ->
    zokrates_of_builtin f (List.map (fun arg -> "(" ^ zokrates_of_expr arg ^ ")") args)
and zokrates_of_lexpr le =
  match le.lexpr with
  | Evar (var, true) -> var
  | Evar (var, false) -> var
  | Eindex (arr, _, index) -> Printf.sprintf "(%s)[%s]" (zokrates_of_lexpr arr) (zokrates_of_expr index)
  | Efield (st, field) -> zokrates_of_lexpr st ^ "." ^ field
  | Ederef _ -> raise (UnsupportedType "pointer")

let rec indent_zokrates_of_cmd su_env ind c =
  match c.cmd with
  | Cskip -> ""
  | Cseq (c1, c2) -> indent_zokrates_of_cmd su_env ind c1 ^ "\n" ^ indent_zokrates_of_cmd su_env ind c2
  | Cdef (ty, var, e) ->
    begin match ty with
    | Tunit -> (* zokrates does not allow void variable *)
      ind ^ zokrates_of_expr e ^ ";"
    | _ ->
      ind ^ Printf.sprintf "%s %s = %s;" (zokrates_of_typ ty) var (zokrates_of_expr e)
    end
  | Ccall (ty, anno, var, f, args) ->
    let call_text = f ^ "(" ^ String.concat ", " (List.map (fun arg -> "(" ^ zokrates_of_expr arg ^ ")") args) ^ ");" in
    begin match ty, anno with
    | Tunit, SANDBOX PLOCAL1 | Tunit, SANDBOX PLOCAL2 -> ""
    | Tunit, _ ->
      ind ^ call_text
    | _, SANDBOX PLOCAL1 | _, SANDBOX PLOCAL2 ->
      raise TODOGen
    | _, _ ->
      ind ^ Printf.sprintf "%s %s = %s;" (zokrates_of_typ ty) var call_text
    end
  | Casgn (le, e) -> ind ^ zokrates_of_lexpr le ^ " = " ^ zokrates_of_expr e ^ ";"
  | Cif (e, c1, c2) ->
    let c1_text = indent_zokrates_of_cmd su_env ind c1 in
    let c2_text = indent_zokrates_of_cmd su_env ind c2 in
    ind ^ "if (" ^ zokrates_of_expr e ^ ")\n" ^ c1_text ^ "\n" ^ ind ^ "else\n" ^ c2_text
  | Cwhile _ -> raise (UnsupportedCmd "while")
  | Csection c -> ind ^ "{\n" ^ indent_zokrates_of_cmd su_env (ind^"  ") c ^ "\n" ^ ind ^ "}"
  | Creturn e ->
    let ret_text = match e.expr with
    | Eunit -> ""
    | _ -> " " ^ zokrates_of_expr e ^ ""
    in
    ind ^ "return" ^ ret_text ^ ";"
  | Cbreak -> raise (UnsupportedCmd "break")
  | Ccontinue -> raise (UnsupportedCmd "continue")
  | Cassert e ->
    match type_of_expr e with
    | Tbool (Public _) -> ind ^ Printf.sprintf "assert(%s);" (zokrates_of_expr e)
    | Tbool (Private _) -> ind ^ Printf.sprintf "assert(%s);" (zokrates_of_expr e)
    | Tbool (Plocal _) -> ind ^ Printf.sprintf "assert(%s);" (zokrates_of_expr e)
    | _ -> raise (FatalInAST "Assertion does not have boolean type")

let is_pvt_in_alias alias =
  match alias with
  | AliasGlob s
  | AliasNorm (s, _) ->
    String.starts_with ~prefix:"pvtin_" s
let is_pub_in_alias alias =
  match alias with
  | AliasGlob s
  | AliasNorm (s, _) ->
    String.starts_with ~prefix:"pubin_" s

let collect_vars prog =
  let pvt_in_var_types = AliasHashtbl.create 10 in
  let pub_in_var_types = AliasHashtbl.create 10 in
  let record_pvt_in_var_type ty alias =
    if not (AliasHashtbl.mem pvt_in_var_types alias) then
      AliasHashtbl.add pvt_in_var_types alias ty
  in
  let record_pub_in_var_type ty alias =
    if not (AliasHashtbl.mem pub_in_var_types alias) then
      AliasHashtbl.add pub_in_var_types alias ty
  in
  let collect_var node =
    match node.cmdinfo_cmd.scmd with
    | SCdef (ty, alias, _) ->
      if is_pvt_in_alias alias then 
        record_pvt_in_var_type ty alias
      else if is_pub_in_alias alias then
        record_pub_in_var_type ty alias
    | _ -> ()
  in
  Seq.iter (fun node ->
    collect_var node
  ) prog;
  (AliasHashtbl.to_seq pvt_in_var_types, AliasHashtbl.to_seq pub_in_var_types)

let output_ou_main oc (*su_env*) _ frag =
  let (witnesses, instances) = collect_vars frag in
  let output_scmd sc =
    match sc.scmd with
    | SCdef (ty, alias, se) ->
      if not (is_pub_in_alias alias || is_pvt_in_alias alias) then (* skip defining witnesses and instances *)
      begin match ty with
      | Tunit -> (* zokrates does not allow void variable *)
        Printf.fprintf oc "  %s;\n" (zokrates_of_sexpr se)
      | _ ->
        Printf.fprintf oc " %s mut %s = %s;\n" (zokrates_of_typ ty) (zokrates_name_of_alias alias) (zokrates_of_sexpr se)
      end
    | SCasgn (sle, se) ->
      Printf.fprintf oc "  %s = %s;\n" (zokrates_of_slexpr sle) (zokrates_of_sexpr se)
    | SCassert se ->
      begin match type_of_sexpr se with
      | Tbool (Private _) -> Printf.fprintf oc "  assert(%s);\n" (zokrates_of_sexpr se)
      | Tbool (Public _)
      | Tbool (Plocal _) -> Printf.fprintf oc "  assert(%s);\n" (zokrates_of_sexpr se)
      | _ -> raise (FatalInGen "assertion does not have boolean type")
      end
    | SCcall (ty, alias, f, args, pubR) ->
      (* sync *)
      List.iter (fun (lv, v) ->
        Printf.fprintf oc "  %s = %s;\n" (zokrates_of_lvalue lv) (zokrates_of_value v)) pubR;
      (* receiver *)
      begin match ty with
      | Tunit -> output_string oc "  "
      | _ -> Printf.fprintf oc "  %s =" (zokrates_lname_of_alias alias)
      end;
      Printf.fprintf oc "%s(%s);\n" f (String.concat ", " (List.map (fun arg -> zokrates_of_sexpr arg) args))
    | SCsandboxcall (ty, kind, alias, f, args) ->
      (* prepare type and variable *)
      begin match ty with
      | Tunit -> output_string oc "  "
      | _ -> Printf.fprintf oc "  %s =" (zokrates_lname_of_alias alias)
      end;
      (* rhs *)
      begin match kind with
      | BLACKBOX1 | BLACKBOX2 ->
        Printf.fprintf oc "%s(%s);\n" f (String.concat ", " (List.map (fun arg -> zokrates_of_sexpr arg) args))
      | PLOCAL1 | PLOCAL2 -> raise TODOGen
      end
  in
  let main_params_text =
    let zokrates_of_witness = function
    | (alias, ty) -> Printf.sprintf "private %s %s" (zokrates_of_typ ty) (zokrates_name_of_alias alias)
    in
    let zokrates_of_instance = function
    | (alias, ty) -> Printf.sprintf "%s %s" (zokrates_of_typ ty) (zokrates_name_of_alias alias)
    in
    String.concat ", " (List.of_seq (Seq.append (Seq.map zokrates_of_witness witnesses) (Seq.map zokrates_of_instance instances)))
  in
  output_string oc ("def main("^main_params_text^") {\n");
  (* output commands *)
  Seq.iter (fun node ->
    output_scmd node.cmdinfo_cmd
  ) frag;
  output_string oc "}\n"

let output_zokrates filename su_env (*gvars*)_ frag (*noc*)_ =
  let oc = open_out filename in
  output_ou_main oc su_env frag;
  close_out oc
