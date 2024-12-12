open Ast
open Util

exception FatalInSim of string

(* symbolic value *********************************************************** *)

type svalue =
  | SVunit
  | SVint of seclvl * int
  | SVfloat of seclvl * float
  | SVbool of seclvl * bool
  | SVref of lvalue_node
  | SVnull
  | SVarray of seclvl * svalue array (* only for array with visible access *)
  | SVstruct of (string, svalue) Hashtbl.t
  | SVsym (* unknown value (K1/K2 during ssim, K2 during dsim) *)

(** For debugging *)
let rec string_of_svalue = function
  | SVunit -> "unit"
  | SVint (_, i) -> string_of_int i
  | SVbool (_, b) -> string_of_bool b
  | SVfloat (_, f) -> string_of_float f
  | SVref lv -> "& " ^ string_of_lvalue_node lv
  | SVnull -> "null"
  | SVarray (_, arr) -> string_of_array arr string_of_svalue
  | SVstruct st ->
    let asgns = Hashtbl.fold (fun field v asgns' -> (field ^ " = " ^ string_of_svalue v) :: asgns') st [] in
    "{" ^ String.concat ", " asgns ^ "}"
  | SVsym -> "SYM"

let _debug_svalue = string_of_svalue

(** Convert an svalue into value.
    It's a partial function, and it returns None whenever there's any SVsym in the input. *)
let rec value_of_K0_svalue = function
  | SVunit -> Some Vunit
  | SVint (_, i) -> Some (Vint i)
  | SVbool (_, b) -> Some (Vbool b)
  | SVfloat (_, f) -> Some (Vfloat f)
  | SVref lv -> Some (Vref lv)
  | SVnull -> Some Vnull
  | SVarray (_, sarr) ->
    let has_k1k2 = ref false in
    let arr = Array.map (fun sv ->
      match value_of_K0_svalue sv with
      | None -> has_k1k2 := true; Vunit
      | Some v -> v
    ) sarr in
    if !has_k1k2 then None
    else Some (Varray arr)
  | SVstruct stbl ->
    let has_k1k2 = ref false in
    let tbl = Hashtbl.create (Hashtbl.length stbl) in
    Hashtbl.iter (fun field sv ->
      match value_of_K0_svalue sv with
      | None -> has_k1k2 := true
      | Some v -> Hashtbl.add tbl field v
    ) stbl;
    if !has_k1k2 then None
    else Some (Vstruct tbl)
  | SVsym -> None

let rec value_of_K0K1_svalue = function
  | SVunit -> Some Vunit
  | SVint (_, i) -> Some (Vint i)
  | SVbool (_, b) -> Some (Vbool b)
  | SVfloat (_, f) -> Some (Vfloat f)
  | SVref lv -> Some (Vref lv)
  | SVnull -> Some Vnull
  | SVarray (_, sarr) ->
    let has_k2 = ref false in
    let arr = Array.map (fun sv ->
      match value_of_K0K1_svalue sv with
      | None -> has_k2 := true; Vunit
      | Some v -> v
    ) sarr in
    if !has_k2 then None
    else Some (Varray arr)
  | SVstruct stbl ->
    let has_k2 = ref false in
    let tbl = Hashtbl.create (Hashtbl.length stbl) in
    Hashtbl.iter (fun field sv ->
      match value_of_K0K1_svalue sv with
      | None -> has_k2 := true
      | Some v -> Hashtbl.add tbl field v
    ) stbl;
    if !has_k2 then None
    else Some (Vstruct tbl)
  | SVsym -> None

let rec svalue_of_value su_env ty v =
  match ty, v with
  | Tunit, Vunit -> SVunit
  | Tint sec, Vint i -> SVint (sec, i)
  | Tbool sec, Vbool b -> SVbool (sec, b)
  | Tfloat sec, Vfloat f -> SVfloat (sec, f)
  | Tref _, Vref lv -> SVref lv
  | Tref _, Vnull -> SVnull
  | Tarray (ty_elem, sec, _), Varray arr ->
    let sarr = Array.map (svalue_of_value su_env ty_elem) arr in
    SVarray (sec, sarr)
  | Tstruct _, Vstruct tbl ->
    let stbl = Hashtbl.create (Hashtbl.length tbl) in
    Hashtbl.iter (fun field v ->
      let ty_field = get_field_type su_env field in
      let sv = svalue_of_value su_env ty_field v in
      Hashtbl.add stbl field sv) tbl;
    SVstruct stbl
  | _ -> raise (FatalInSim "svalue of type does not match")

(** Deep copy an svalue *)
let rec copy_svalue = function
  | SVarray (sec, arr) ->
    let arr' = Array.make (Array.length arr) SVunit in
    Array.iteri (fun i v -> Array.set arr' i (copy_svalue v)) arr;
    SVarray (sec, arr')
  | SVstruct tbl ->
    let tbl' = Hashtbl.create (Hashtbl.length tbl) in
    Hashtbl.iter (fun field v -> Hashtbl.add tbl' field (copy_svalue v)) tbl;
    SVstruct tbl'
  | v -> v

(** Construct svalue based on type. Always succeed.
    The only meaningful cases are Tarray and Tzkram where we need to construct
    arrays as placeholders, so that latter we can fill in values. *)
let rec uninit_svalue_of_typ is_dsim su_env ty =
  let is_known_atom sec =
    match knwlvl_of_seclvl sec with
    | K0 -> true
    | K1 -> is_dsim
    | K2 -> false
  in
  match ty with
  | Tunit -> SVunit
  | Tint sec ->
    if is_known_atom sec then SVint (sec, 0)
    else SVsym
  | Tbool sec ->
    if is_known_atom sec then SVbool (sec, false)
    else SVsym
  | Tfloat sec ->
    if is_known_atom sec then SVfloat (sec, 0.)
    else SVsym
  | Tarray (elem_ty, sec, size) ->
    let max_klvl = if is_dsim then K1 else K0 in
    let klvl = knwlvl_of_seclvl sec in
    if knwlvl_le klvl max_klvl then
      let default_elem = uninit_svalue_of_typ is_dsim su_env elem_ty in
      let sarr = Array.init size (fun _ -> copy_svalue default_elem) in
      SVarray (sec, sarr)
    else SVsym
  | Tstruct st_name ->
    let st = find_struct su_env st_name in
    let tbl = Hashtbl.create (List.length st.struct_fields) in
    List.iter (fun (ty, field) ->
      let v = uninit_svalue_of_typ is_dsim su_env ty in
      Hashtbl.add tbl field v) st.struct_fields;
    SVstruct tbl
  | Tref _ -> SVnull

let lvaluemap_unions =
  List.fold_left (LValueMap.union (fun _ v1 _ -> Some v1)) LValueMap.empty

let rec indivisible_K0_lvalues su_env lv_base sv_base =
  let base_ty = type_of_lvalue lv_base in
  match base_ty with
  | Tint _ | Tbool _ | Tfloat _ | Tref _ ->
    begin match value_of_K0_svalue sv_base with
    | Some v -> LValueMap.singleton lv_base v
    | None -> LValueMap.empty
    end
  | Tunit -> LValueMap.empty
  | Tarray (ty_index, sec, size) ->
    begin match sec, sv_base with
    | Public K0Public, SVarray (_, arr) ->
      let res = ref LValueMap.empty in
      for idx = 0 to size - 1 do
        let lv_index = mk_lvalue (Vindex (lv_base, sec, idx)) ty_index in
        let sv_index = Array.get arr idx in
        let map_index = indivisible_K0_lvalues su_env lv_index sv_index in
        res := LValueMap.union (fun _ v1 _ -> Some v1) !res map_index
      done;
      !res
    | _ -> LValueMap.empty
    end
  | Tstruct st_name ->
    begin match sv_base with
    | SVstruct tbl ->
      let st = Hashtbl.find su_env.su_structs st_name in
      (* collect all fields *)
      lvaluemap_unions @@ List.map (fun (ty, field) ->
        let lv_field = mk_lvalue (Vfield (lv_base, field)) ty in
        let sv_field = Hashtbl.find tbl field in
        indivisible_K0_lvalues su_env lv_field sv_field
      ) st.struct_fields
    | _ -> raise (FatalInSim "struct is not stored as SVstruct")
    end

let rec indivisible_K1K2_lvalues su_env lv_base =
  let base_ty = type_of_lvalue lv_base in
  match base_ty with
  | Tint (Public l) | Tbool (Public l) | Tfloat (Public l) ->
    if l = K0Public then []
    else [lv_base]
  | Tint (Private _) | Tbool (Private _) | Tfloat (Private _)
  | Tint (Plocal _) | Tbool (Plocal _) | Tfloat (Plocal _) ->
    [lv_base]
  | Tunit | Tref _ -> []
  | Tarray (_, sec, size) ->
    begin match sec with
    | Private _ ->
      (* zkram is indivisible at the moment *)
      [lv_base]
    | Public K0Public ->
      (* collect all its elements *)
      let res = ref [] in
      let ty_index = type_of_element base_ty in
      for idx = (size-1) downto 0 do
        let lv_index = mk_lvalue (Vindex (lv_base, sec, idx)) ty_index in
        res := (indivisible_K1K2_lvalues su_env lv_index) @ !res
      done;
      !res
    | _ -> [lv_base]
    end
  | Tstruct st_name ->
    let st = Hashtbl.find su_env.su_structs st_name in
    (* collect all fields *)
    let res = ref [] in
    List.iter (fun (ty, field) ->
      let lv_field = mk_lvalue (Vfield (lv_base, field)) ty in
      res := (indivisible_K1K2_lvalues su_env lv_field) @ !res
    ) st.struct_fields;
    !res

(** Convert a simplified sexpr to svalue. Always succeed.
    Used in both ssim and dsim. *)
let rec svalue_of_sexpr is_dsim su_env base_se =
  let convert_arr sec se_inits =
    let elem_ty, size = match type_of_sexpr base_se with
    | Tarray (elem_ty, _, size) -> elem_ty, size
    | ty -> raise (FatalInSim (string_of_typ ty ^ " is not an array type"))
    in
    let sv_inits = List.map (svalue_of_sexpr is_dsim su_env) se_inits in
    (* firstly init the entire array with placeholder *)
    let sarr = Array.make size SVunit in
    let inits_len = List.length se_inits in
    (* then fill in previous elements *)
    List.iteri (fun idx sv_init ->
      if idx < size then Array.set sarr idx sv_init) sv_inits;
    (* then fill in default values *)
    if inits_len < size then begin
      let default_elem = uninit_svalue_of_typ is_dsim su_env elem_ty in
      repeat_n (fun offset ->
        Array.set sarr (inits_len + offset) default_elem) (size - inits_len)
    end;
    SVarray (sec, sarr)
  in
  let ty = type_of_sexpr base_se in
  match base_se.sexpr with
  | SEunit -> SVunit
  | SEint i -> begin match ty with
    | Tint sec -> SVint (sec, i)
    | _ -> raise (FatalInSim "Type wrong")
    end
  | SEfloat f -> begin match ty with
    | Tfloat sec ->  SVfloat (sec, f)
    | _ -> raise (FatalInSim "Type wrong")
    end
  | SEbool b -> begin match ty with
    | Tbool sec ->  SVbool (sec, b)
    | _ -> raise (FatalInSim "Type wrong")
    end
  | SEnull -> SVnull
  | SEref lv -> SVref lv
  | SEarrayinit (sec, se_inits) ->
    let max_klvl = if is_dsim then K1 else K0 in
    let klvl = knwlvl_of_seclvl sec in
    if knwlvl_le klvl max_klvl then
      convert_arr sec se_inits
    else
      SVsym
  | SEstructinit se_asgns ->
    let stbl = Hashtbl.create (List.length se_asgns) in
    (* add all fields' public values *)
    List.iter (fun (field, se_asgn) ->
      Hashtbl.add stbl field (svalue_of_sexpr is_dsim su_env se_asgn)) se_asgns;
    SVstruct stbl
  | SElexpr _ -> SVsym (* The lexpr is already simplified, so no need to load. *)
  | SEbuiltin (f_name, _) -> (* The builtin function can not be evaluated to a meaningful value at the current stage (ssim/dsim), so just use a default value. *)
    let f_sig = Hashtbl.find Builtin.builtin_types f_name in
    let ret_ty = f_sig.funsig_return in
    uninit_svalue_of_typ is_dsim su_env ret_ty

let rec sexpr_of_svalue sv lv =
  let ret raw_se = mk_sexpr raw_se (type_of_lvalue lv) Location.none in
  match sv with
  | SVunit -> ret SEunit
  | SVint (_, i) -> ret (SEint i)
  | SVbool (_, b) -> ret (SEbool b) 
  | SVfloat (_, f) -> ret (SEfloat f) 
  | SVnull -> ret SEnull
  | SVref lv_ref -> ret (SEref lv_ref)
  | SVsym ->
    let sle = slexpr_of_lvalue lv in
    ret (SElexpr sle)
  | SVarray (sec, arr) ->
    let ty_arr = type_of_lvalue lv in
    let ty_elem = type_of_element ty_arr in
    let se_inits = List.mapi (fun i sv_elem ->
      let lv_elem = mk_lvalue (Vindex (lv, sec, i)) ty_elem in
      let se_elem = sexpr_of_svalue sv_elem lv_elem in
      se_elem) (Array.to_list arr)
    in
    ret (SEarrayinit (sec, se_inits))
  | SVstruct tbl ->
    let ty_st = type_of_lvalue lv in
    let se_asgns = List.map (fun (field, sv) ->
      let lv_field = mk_lvalue (Vfield (lv, field)) ty_st in
      (field, sexpr_of_svalue sv lv_field)) (List.of_seq (Hashtbl.to_seq tbl))
    in
    ret (SEstructinit se_asgns)
