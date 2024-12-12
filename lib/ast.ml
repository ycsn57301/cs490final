(* open Util *)
exception FatalInAST of string

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)

type binop =
  | Oadd
  | Osub
  | Omul
  | Odiv
  | Omod
  | Oeq
  | One
  | Ogt
  | Oge
  | Olt
  | Ole
  | Oand
  | Oor
  | Oland
  | Olor
  | Olxor
  | Olsl
  | Olsr

type uop =
  | Oneg
  | Onot
  | Olnot

type publvl =
  | K0Public
  | K1Public
  | K2Public

type pvtlvl =
  | K1Private
  | K2Private

type plclvl =
  | K1Plocal
  | K2Plocal

type seclvl =
  | Public of publvl
  | Private of pvtlvl
  | Plocal of plclvl

let pvt1 = Private K1Private
let pvt2 = Private K2Private
let pub0 = Public K0Public
let pub1 = Public K1Public
let pub2 = Public K2Public
let plc1 = Plocal K1Plocal
let plc2 = Plocal K2Plocal

let int_of_publvl = function
  | K0Public -> 0
  | K1Public -> 1
  | K2Public -> 2

let int_of_pvtlvl = function
  | K1Private -> 1
  | K2Private -> 2

let int_of_plclvl = function
  | K1Plocal -> 1
  | K2Plocal -> 2

let publvl_le l1 l2 =
  int_of_publvl l1 <= int_of_publvl l2

let publvl_lt l1 l2 =
  int_of_publvl l1 < int_of_publvl l2

let pvtlvl_le l1 l2 =
  int_of_pvtlvl l1 <= int_of_pvtlvl l2

let pvtlvl_lt l1 l2 =
  int_of_pvtlvl l1 < int_of_pvtlvl l2

let plclvl_le l1 l2 =
  int_of_plclvl l1 <= int_of_plclvl l2

let plclvl_lt l1 l2 =
  int_of_plclvl l1 < int_of_plclvl l2

(* let publvl_of_pvtlvl = function
  | K1Private -> K1Public
  | K2Private -> K2Public
*)
let pvtlvl_of_publvl = function
  | K0Public | K1Public -> K1Private
  | K2Public -> K2Private

let plclvl_of_publvl = function
  | K0Public | K1Public -> K1Plocal
  | K2Public -> K2Plocal

let publvl_of_pvtlvl = function
  | K1Private -> K1Public
  | K2Private -> K2Public

let publvl_of_plclvl = function
  | K1Plocal -> K1Public
  | K2Plocal -> K2Public

let plclvl_of_pvtlvl = function
  | K1Private -> K1Plocal
  | K2Private -> K2Plocal

let pvtlvl_of_plclvl = function
  | K1Plocal -> K1Private
  | K2Plocal -> K2Private

(** only allow public to implicitly convert to private/plocal, private to implicitly convert to plocal.
    This is not a total order as K1Private and K2Public are not comparable. *)
let seclvl_le sec1 sec2 =
  match sec1, sec2 with
  | Public l1, Public l2 -> publvl_le l1 l2
  | Private l1, Private l2 -> pvtlvl_le l1 l2
  | Plocal l1, Plocal l2 -> plclvl_le l1 l2
  | Public l1, Private l2 -> int_of_publvl l1 <= int_of_pvtlvl l2
  | Private _, Public _ -> false
  | Public l1, Plocal l2 -> int_of_publvl l1 <= int_of_plclvl l2
  | Plocal _, Public _ -> false
  | Private l1, Plocal l2 -> int_of_pvtlvl l1 <= int_of_plclvl l2
  | Plocal _, Private _ -> false

let publvl_join l1 l2 =
  if publvl_le l1 l2 then l2 else l1

let pvtlvl_join l1 l2 =
  if pvtlvl_le l1 l2 then l2 else l1

let plclvl_join l1 l2 =
  if plclvl_le l1 l2 then l2 else l1

(** Find the least upper bound of two security levels. *)
let seclvl_join sec1 sec2 =
  match sec1, sec2 with
  | Public l1, Public l2 -> Public (publvl_join l1 l2)
  | Private l1, Private l2 -> Private (pvtlvl_join l1 l2)
  | Plocal l1, Plocal l2 -> Plocal (plclvl_join l1 l2)
  | Public l1, Private l2 | Private l2, Public l1 ->
    let l1' = pvtlvl_of_publvl l1 in
    Private (pvtlvl_join l1' l2)
  | Public l1, Plocal l2 | Plocal l2, Public l1 ->
    let l1' = plclvl_of_publvl l1 in
    Plocal (plclvl_join l1' l2)
  | Private l1, Plocal l2 | Plocal l2, Private l1 ->
    let l1' = plclvl_of_pvtlvl l1 in
    Plocal (plclvl_join l1' l2)

type knwlvl =
  | K0 (* both parties know at compile time *)
  | K1 (* prover know before run *)
  | K2 (* only known at runtime *)

let string_of_knwlvl = function
  | K0 -> "KNW0"
  | K1 -> "KNW1"
  | K2 -> "KNW2"

let knwlvl_of_publvl = function
  | K0Public -> K0
  | K1Public -> K1
  | K2Public -> K2

let knwlvl_of_pvtlvl = function
  | K1Private -> K1
  | K2Private -> K2

let knwlvl_of_plclvl = function
  | K1Plocal -> K1
  | K2Plocal -> K2

let publvl_of_knwlvl = function
  | K0 -> K0Public
  | K1 -> K1Public
  | K2 -> K2Public

let pvtlvl_of_knwlvl = function
  | K0 -> raise (FatalInAST "pvtlvl can not be K0")
  | K1 -> K1Private
  | K2 -> K2Private

let plclvl_of_knwlvl = function
  | K0 -> raise (FatalInAST "plclvl can not be K0")
  | K1 -> K1Plocal
  | K2 -> K2Plocal

let knwlvl_of_seclvl = function
  | Public l -> knwlvl_of_publvl l
  | Private l -> knwlvl_of_pvtlvl l
  | Plocal l -> knwlvl_of_plclvl l

let knwlvl_le l1 l2 =
  match l1, l2 with
  | K0, _ -> true
  | K1, K1 | K1, K2 -> true
  | K2, K2 -> true
  | _ -> false

let knwlvl_lt l1 l2 =
  match l1, l2 with
  | K0, K1
  | K0, K2
  | K1, K2 -> true
  | _ -> false

let knwlvl_max l1 l2 =
  if knwlvl_le l1 l2 then l2 else l1

type typ =
  | Tunit
  | Tbool of seclvl
  | Tint of seclvl
  | Tfloat of seclvl
  | Tarray of typ * seclvl * int
  | Tref of typ
  | Tstruct of string

let functor_Tint sec = Tint sec
let functor_Tbool sec = Tbool sec
let functor_Tfloat sec = Tfloat sec

type callconv =
  | CCval
  | CCref

type sandbox_anno_kind =
  | PLOCAL1
  | PLOCAL2
  | BLACKBOX1
  | BLACKBOX2

type fun_anno_kind =
  | NORMAL
  | ATOMIC
  | SANDBOX of sandbox_anno_kind

let seclvl_of_fun_anno_kind = function
  | NORMAL | ATOMIC -> Public K0Public
  | SANDBOX a ->
    match a with
    | PLOCAL1 -> Plocal K1Plocal
    | PLOCAL2 -> Plocal K2Plocal
    | BLACKBOX1 -> Public K1Public
    | BLACKBOX2 -> Public K2Public

type funsig = {
  funsig_params : (typ * callconv) list;
  funsig_return : typ;
  funsig_anno : fun_anno_kind
}

let string_of_binop = function
  | Oadd -> "+"
  | Osub -> "-"
  | Omul -> "*"
  | Odiv -> "/"
  | Omod -> "%"
  | Oeq -> "="
  | One -> "!="
  | Oge -> ">="
  | Ole -> "<="
  | Ogt -> ">"
  | Olt -> "<"
  | Oand -> "&&"
  | Oor -> "||"
  | Oland -> "&"
  | Olor -> "|"
  | Olxor -> "^"
  | Olsl -> "<<"
  | Olsr -> ">>"

let string_of_uop = function
  | Oneg -> "-"
  | Onot -> "!"
  | Olnot -> "~"

let name_of_binop = function
  | Oadd -> "add"
  | Osub -> "sub"
  | Omul -> "mul"
  | Odiv -> "div"
  | Omod -> "mod"
  | Oeq -> "eq"
  | One -> "ne"
  | Oge -> "ge"
  | Ole -> "le"
  | Ogt -> "gt"
  | Olt -> "lt"
  | Oand -> "and"
  | Oor -> "or"
  | Oland -> "land"
  | Olor -> "lor"
  | Olxor -> "lxor"
  | Olsl -> "lsl"
  | Olsr -> "lsr"

let name_of_uop = function
  | Oneg -> "neg"
  | Onot -> "not"
  | Olnot -> "lnot"

let string_of_publvl = function
  | K0Public -> "pub0"
  | K1Public -> "pub1"
  | K2Public -> "pub2"

let string_of_pvtlvl = function
  | K1Private -> "pvt1"
  | K2Private -> "pvt2"

let string_of_plclvl = function
  | K1Plocal -> "plc1"
  | K2Plocal -> "plc2"

let string_of_seclvl = function
  | Private lvl -> string_of_pvtlvl lvl
  | Public lvl -> string_of_publvl lvl
  | Plocal lvl -> string_of_plclvl lvl

let rec string_of_typ = function
  | Tunit -> "unit"
  | Tint sec -> string_of_seclvl sec ^ " int"
  | Tfloat sec -> string_of_seclvl sec ^ " float"
  | Tbool sec -> string_of_seclvl sec ^ " bool"
  | Tarray (ty_elem, lvl, size) -> string_of_typ ty_elem ^ "[" ^ string_of_seclvl lvl ^ " " ^ string_of_int size ^ "]"
  | Tstruct st -> "struct " ^ st
  | Tref ty -> string_of_typ ty ^ " *"

(* let rec string_of_rawtyp = function
  | Tunit -> "unit"
  | Tint _ -> "int"
  | Tfloat _ -> "float"
  | Tbool _ -> "bool"
  | Tarray (ty_elem, size) | Tzkram (ty_elem, size) -> string_of_rawtyp ty_elem ^ "[" ^ string_of_int size ^ "]"
  | Tstruct st -> "struct " ^ st
  | Tref ty -> string_of_rawtyp ty ^ " *" *)

let string_of_anno_kind = function
  | NORMAL -> ""
  | ATOMIC -> "atomic "
  | SANDBOX a ->
    match a with
    | PLOCAL1 -> "plocal1 "
    | PLOCAL2 -> "plocal2 "
    | BLACKBOX1 -> "blackbox1 "
    | BLACKBOX2 -> "blackbox2 "

(** Return the type of an array's element *)
let type_of_element arr_ty =
  match arr_ty with
  | Tarray (elem_ty, _, _) -> elem_ty
  | _ -> raise (FatalInAST (string_of_typ arr_ty ^ " is not an array type"))

(** Return the array size from an array's type *)
let array_size_from_type arr_ty =
  match arr_ty with
  | Tarray (_, _, size) -> size
  | _ -> raise (FatalInAST (string_of_typ arr_ty ^ " is not an array type"))

(* Parsing Syntax Tree ********************************************************)
type p_expr =
  | PEunit
  | PEbool of bool
  | PEint of int
  | PEfloat of float
  | PEnull
  | PEref of p_expr_node
  | PEcall of string * p_expr_node list
  | PEbinary of p_expr_node * binop * p_expr_node
  | PEunary of uop * p_expr_node
  | PEarrayinit of p_expr_node list
  | PEstructinit of (string * p_expr_node) list
  | PEvar of string
  | PEindex of p_expr_node * p_expr_node
  | PEfield of p_expr_node * string
  | PEderef of p_expr_node
and p_expr_node = {
  p_expr : p_expr;
  p_expr_loc : Location.t;
}

let loc_of_p_expr pe = pe.p_expr_loc

let mk_p_expr pe loc = {
  p_expr = pe;
  p_expr_loc = loc;
}

type p_cmd =
  | PCskip
  | PCseq of p_cmd_node * p_cmd_node
  | PCdef of typ * string * p_expr_node
  | PCasgn of p_expr_node * p_expr_node
  | PCeval of p_expr_node
  | PCif of p_expr_node * p_cmd_node * p_cmd_node
  | PCfor of p_cmd_node * p_expr_node * p_cmd_node * p_cmd_node (* init, check, step, body *)
  | PCwhile of p_expr_node * p_cmd_node (* check, body *)
  | PCsection of p_cmd_node
  | PCreturn of p_expr_node
  | PCbreak
  | PCcontinue
  | PCassert of p_expr_node
and p_cmd_node = {
  p_cmd : p_cmd;
  p_cmd_loc : Location.t;
}

let loc_of_p_cmd pc = pc.p_cmd_loc

let mk_p_cmd pc loc = {
  p_cmd = pc;
  p_cmd_loc = loc;
}

type p_structdef = {
  pstruct_name : string;
  pstruct_fields : (typ * string) list;
}
type p_structdef_node = {
  p_structdef : p_structdef;
  p_structdef_loc : Location.t;
}

let loc_of_p_structdef sd = sd.p_structdef_loc

type p_gvardef = {
  pgvar_typ : typ;
  pgvar_name : string;
  pgvar_init : p_expr_node;
}
type p_gvardef_node = {
  p_gvardef : p_gvardef;
  p_gvardef_loc : Location.t;
}

let loc_of_p_gvardef vd = vd.p_gvardef_loc

type p_fundef = {
  pfun_anno : fun_anno_kind;
  pfun_name : string;
  pfun_ret_typ : typ;
  pfun_params : (typ * string * callconv) list;
  pfun_body : p_cmd_node;
}
type p_fundef_node = {
  p_fundef : p_fundef;
  p_fundef_loc : Location.t;
}

let loc_of_p_fundef fd = fd.p_fundef_loc

type p_xfundecl = {
  pxfun_name : string;
  pxfun_ret_typ : typ;
  pxfun_params : (typ * callconv) list;
  pxfun_anno : fun_anno_kind;
}
type p_xfundecl_node = {
  p_xfundecl : p_xfundecl;
  p_xfundecl_loc : Location.t;
}

type p_top =
  | PTstructdef of p_structdef_node
  | PTgvardef of p_gvardef_node
  | PTfundef of p_fundef_node
  | PTxfundecl of p_xfundecl_node

let sig_of_p_fundef fd =
  let params = List.map (fun (ty, _, cc) -> (ty, cc)) fd.pfun_params in
  { funsig_params = params;
    funsig_return = fd.pfun_ret_typ;
    funsig_anno = fd.pfun_anno
  }

let sig_of_p_xfundecl xd =
  { funsig_params = xd.pxfun_params;
    funsig_return = xd.pxfun_ret_typ;
    funsig_anno = xd.pxfun_anno
  }

let rec string_of_p_expr = function
  | PEunit -> ""
  | PEbool b -> string_of_bool b
  | PEint n -> string_of_int n
  | PEfloat f -> Printf.sprintf "%f" f
  | PEnull -> "null"
  | PEref le -> "& " ^ string_of_p_expr_node le
  | PEcall (f, args) ->
    f ^ "(" ^ String.concat ", " (List.map string_of_p_expr_node args) ^ ")"
  | PEbinary (e1, op, e2) ->
    string_of_p_expr_node e1 ^ " " ^ string_of_binop op ^ " " ^ string_of_p_expr_node e2
  | PEunary (op, e) -> string_of_uop op ^ " " ^ string_of_p_expr_node e
  | PEarrayinit inits ->
    "{" ^ String.concat ", " (List.map string_of_p_expr_node inits) ^ ")"
  | PEstructinit asgns -> "{" ^ String.concat ", " (List.map (fun (field, pe) ->
    "." ^ field ^ " = " ^ string_of_p_expr_node pe) asgns) ^ "}"
  | PEvar v -> v
  | PEindex (arr, index) -> string_of_p_expr_node arr ^ "[" ^ string_of_p_expr_node index ^ "]"
  | PEfield (st, field) -> string_of_p_expr_node st ^ "." ^ field
  | PEderef e -> "* " ^ string_of_p_expr_node e
and string_of_p_expr_node pe = string_of_p_expr pe.p_expr

let rec indent_string_of_p_cmd ind c =
  match c with
  | PCskip -> ""
  | PCseq (c1, c2) ->
    indent_string_of_p_cmd_node ind c1 ^ "\n" ^
    indent_string_of_p_cmd_node ind c2
  | PCdef (ty, var, e) ->
    ind ^ string_of_typ ty ^ " " ^ var ^ " = " ^ string_of_p_expr_node e ^ ";"
  | PCasgn (le, e) ->
    ind ^ string_of_p_expr_node le ^ " = " ^ string_of_p_expr_node e ^ ";"
  | PCeval e -> ind ^ string_of_p_expr_node e ^ ";"
  | PCif (e, c1, c2) ->
    ind ^ "if " ^ string_of_p_expr_node e ^ "\n" ^
    indent_string_of_p_cmd_node ind c1 ^ "\n" ^ ind ^
    "else\n" ^ indent_string_of_p_cmd_node ind c2
  | PCfor (init, check, step, c) ->
    ind ^ "for " ^ indent_string_of_p_cmd_node "" init ^ " " ^
    string_of_p_expr_node check ^ "; " ^
    indent_string_of_p_cmd_node "" step ^ "\n" ^
    indent_string_of_p_cmd_node ind c
  | PCwhile (e, c) ->
    ind ^ "while "^ string_of_p_expr_node e ^ " \n" ^
    indent_string_of_p_cmd_node ind c
  | PCsection c ->
    ind ^ "{\n" ^ indent_string_of_p_cmd_node (ind^"  ") c ^ "\n" ^ ind ^ "}"
  | PCreturn e -> ind ^ "return " ^ string_of_p_expr_node e ^ ";"
  | PCbreak -> ind ^ "break;"
  | PCcontinue -> ind ^ "continue";
  | PCassert e -> ind ^ "assert " ^ string_of_p_expr_node e ^ ";"
and indent_string_of_p_cmd_node ind c = indent_string_of_p_cmd ind c.p_cmd

let string_of_p_cmd c = indent_string_of_p_cmd "" c
let string_of_p_cmd_node c = string_of_p_cmd c.p_cmd

let string_of_p_fundef fd =
  let string_of_param (ty, name, cc) =
    string_of_typ ty ^ " " ^ (if cc = CCref then "& " else "") ^ name
  in
  string_of_anno_kind fd.pfun_anno ^ " " ^
  string_of_typ fd.pfun_ret_typ ^ " " ^ fd.pfun_name ^ "(" ^
  String.concat ", " (List.map string_of_param fd.pfun_params) ^
  ")" ^ "{\n" ^ indent_string_of_p_cmd_node "  " fd.pfun_body ^ "\n}"
let string_of_p_fundef_node fd = string_of_p_fundef fd.p_fundef

let string_of_p_xfundecl xd =
  let string_of_param (ty, cc) =
    string_of_typ ty ^ " " ^ (if cc = CCref then "&" else "")
  in
  string_of_typ xd.pxfun_ret_typ ^ " " ^ xd.pxfun_name ^ "(" ^
  String.concat ", " (List.map string_of_param xd.pxfun_params) ^
  ")"
let string_of_p_xfundecl_node xd = string_of_p_xfundecl xd.p_xfundecl

let string_of_p_gvardef vd =
  let ty = vd.pgvar_typ in
  string_of_typ ty ^ " " ^ vd.pgvar_name ^ " = " ^
  string_of_p_expr_node vd.pgvar_init ^ ";"
let string_of_p_gvardef_node vd = string_of_p_gvardef vd.p_gvardef

let string_of_p_structdef sd =
  "struct " ^ sd.pstruct_name ^ " {\n" ^
  String.concat "\n" (List.map (fun (ty, field) ->
    "  " ^ string_of_typ ty ^ " " ^ field ^ ";") sd.pstruct_fields) ^
  "\n}"
let string_of_p_structdef_node sd = string_of_p_structdef sd.p_structdef

let string_of_p_top = function
  | PTfundef fd -> string_of_p_fundef_node fd
  | PTgvardef vd -> string_of_p_gvardef_node vd
  | PTstructdef sd -> string_of_p_structdef_node sd
  | PTxfundecl xd -> string_of_p_xfundecl_node xd

(* Abstract Syntax Tree *******************************************************)
type expr_meta = {
  expr_type : typ;
  expr_loc : Location.t
}
type lexpr_meta = {
  lexpr_type : typ;
  lexpr_loc : Location.t;
}
type expr =
  | Eunit
  | Ebool of bool
  | Eint of int
  | Efloat of float
  | Enull
  | Elexpr of lexpr_node
  | Eref of lexpr_node
  (* | Ecall of string * expr_node list *)
  | Ebuiltin of string * expr_node list
  | Earrayinit of seclvl * expr_node list (* init list *)
  | Estructinit of (string * expr_node) list (* field assignments *)
and expr_node = {
  expr : expr;
  expr_meta : expr_meta
}
and lexpr =
  | Evar of string * bool (* true means it's global variable, otherwise it's local *)
  | Eindex of lexpr_node * seclvl * expr_node (* array, seclvl, index *)
  | Efield of lexpr_node * string (* struct, field name *)
  | Ederef of expr_node
and lexpr_node = {
  lexpr : lexpr;
  lexpr_meta : lexpr_meta
}

let mk_expr e ty loc = {
  expr = e;
  expr_meta = {
    expr_type = ty;
    expr_loc = loc
  }
}

let mk_lexpr le ty loc = {
  lexpr = le;
  lexpr_meta = {
    lexpr_type = ty;
    lexpr_loc = loc;
  }
}

let type_of_expr e = e.expr_meta.expr_type
let type_of_lexpr le = le.lexpr_meta.lexpr_type

let loc_of_expr e = e.expr_meta.expr_loc
let loc_of_lexpr le = le.lexpr_meta.lexpr_loc

type cmd_meta = {
  cmd_loc : Location.t
}
type cmd =
| Cskip
| Cseq of cmd_node * cmd_node
| Cdef of typ * string * expr_node
| Ccall of typ * fun_anno_kind * string * string * expr_node list (* type, kind, receiver, function name, arguments *)
| Casgn of lexpr_node * expr_node
| Cif of expr_node * cmd_node * cmd_node
| Cwhile of expr_node * cmd_node
| Csection of cmd_node
| Creturn of expr_node
| Cbreak
| Ccontinue
| Cassert of expr_node
and cmd_node = {
  cmd : cmd;
  cmd_meta : cmd_meta
}

let mk_cmd c loc = {
  cmd = c;
  cmd_meta = {
    cmd_loc = loc;
  }
}

let loc_of_cmd c = c.cmd_meta.cmd_loc

type gvardef_meta = {
  gvardef_loc : Location.t
}
type gvardef = {
  gvar_typ : typ;
  gvar_name : string;
  gvar_init : expr_node;
}
type gvardef_node = {
  gvardef : gvardef;
  gvardef_meta : gvardef_meta
}

let loc_of_gvardef gd = gd.gvardef_meta.gvardef_loc

type fundef_meta = {
  fundef_loc : Location.t
}
type fundef = {
  fun_anno : fun_anno_kind;
  fun_name : string;
  fun_ret_typ : typ;
  fun_params : (typ * string) list;
  fun_body : cmd_node;
}
type fundef_node = {
  fundef : fundef;
  fundef_meta : fundef_meta
}

type structdef_meta = {
  structdef_loc : Location.t
}
type structdef = {
  struct_name : string;
  struct_fields : (typ * string) list; (* TODO: use map instead *)
}
type structdef_node = {
  structdef : structdef;
  structdef_meta : structdef_meta
}

let rec string_of_expr e =
  match e with
  | Eunit -> ""
  | Ebool b -> string_of_bool b
  | Eint n -> string_of_int n
  | Efloat f -> Printf.sprintf "%f" f
  | Enull -> "null"
  | Elexpr le -> string_of_lexpr_node le
  | Eref le -> "& " ^ string_of_lexpr_node le
  | Ebuiltin (f, args) -> f ^ "(" ^ String.concat ", " (List.map string_of_expr_node args) ^ ")"
  | Earrayinit (sec, inits) ->
    string_of_seclvl sec ^ " {" ^ String.concat ", " (List.map string_of_expr_node inits) ^ "}"
  | Estructinit asgns ->
    "{" ^ String.concat ", " (List.map (fun (field, e) ->
    "." ^ field ^ " = " ^ string_of_expr_node e) asgns) ^ "}"
and string_of_expr_node e = string_of_expr e.expr
and string_of_lexpr le =
  match le with
  | Evar (v, _) -> v
  | Eindex (arr, sec, index) -> string_of_lexpr_node arr ^ "[" ^ string_of_seclvl sec ^ " " ^ string_of_expr_node index ^ "]"
  | Efield (st, field) -> string_of_lexpr_node st ^ "." ^ field
  | Ederef e -> "* " ^ string_of_expr_node e
and string_of_lexpr_node le = string_of_lexpr le.lexpr

let rec indent_string_of_cmd ind c =
  match c with
  | Cskip -> ""
  | Cseq (c1, c2) -> indent_string_of_cmd_node ind c1 ^ "\n" ^ indent_string_of_cmd_node ind c2
  | Cdef (ty, var, e) -> ind ^ string_of_typ ty ^ " " ^ var ^ " = " ^ string_of_expr_node e ^ ";"
  | Ccall (ty, _, var, f, args) -> ind ^ string_of_typ ty ^ " " ^ var ^ " = " ^ f ^ "(" ^ String.concat ", " (List.map string_of_expr_node args) ^ ");"
  | Casgn (le, e) -> ind ^ string_of_lexpr_node le ^ " = " ^ string_of_expr_node e ^ ";"
  | Cif (e, c1, c2) ->
    ind ^ "if (" ^ string_of_expr_node e ^ ")\n" ^
    indent_string_of_cmd_node ind c1 ^ "\n" ^ ind ^
    "else\n" ^ indent_string_of_cmd_node ind c2
  | Cwhile (e, c) ->
    ind ^ "while ("^ string_of_expr_node e ^ ")\n" ^
    indent_string_of_cmd_node ind c
  | Csection c -> ind ^ "{\n" ^ indent_string_of_cmd_node (ind^"  ") c ^ "\n" ^ ind ^ "}"
  | Creturn e -> ind ^ "return " ^ string_of_expr_node e ^ ";"
  | Cbreak -> ind ^ "break;"
  | Ccontinue -> ind ^ "continue;"
  | Cassert e -> ind ^ "assert " ^ string_of_expr_node e ^ ";"
and indent_string_of_cmd_node ind c = indent_string_of_cmd ind c.cmd

let string_of_cmd c = indent_string_of_cmd "" c
let string_of_cmd_node c = string_of_cmd c.cmd

let string_of_fundef fd =
  let body = indent_string_of_cmd_node "  " fd.fun_body in
  string_of_typ fd.fun_ret_typ ^ " " ^ fd.fun_name ^ "(" ^
  String.concat ", " (List.map (fun (ty, v) -> string_of_typ ty ^ " " ^ v) fd.fun_params) ^
  ")" ^ "{\n" ^ body ^ "\n}"
let string_of_fundef_node fd = string_of_fundef fd.fundef

let string_of_gvardef vd =
  let ty = vd.gvar_typ in
  string_of_typ ty ^ " " ^ vd.gvar_name ^ " = " ^ string_of_expr_node vd.gvar_init ^ ";"
let string_of_gvardef_node vd = string_of_gvardef vd.gvardef

let string_of_structdef sd =
  "struct " ^ sd.struct_name ^ " {\n" ^
  String.concat "\n" (List.map (fun (ty, field) ->
    "  " ^ string_of_typ ty ^ " " ^ field ^ ";") sd.struct_fields) ^
  "\n}"
let string_of_structdef_node sd = string_of_structdef sd.structdef

(* struct and union environment ******************************************* *)

exception UndefinedStruct of string
exception UndefinedField of string

type struct_union_env =
{
  su_structs : (string, structdef) Hashtbl.t; (* struct name -> struct def *)
  su_fields : (string, string) Hashtbl.t; (* field name -> struct name. Provide a fast way to lookup field info *)
}

let find_struct su_env st_name =
  try
    Hashtbl.find su_env.su_structs st_name
  with Not_found -> raise (UndefinedStruct st_name)

let find_field su_env field =
  try
    Hashtbl.find su_env.su_fields field
  with Not_found -> raise (UndefinedField field)

let get_field_type su_env field =
  let st_name = find_field su_env field in
  let sd = find_struct su_env st_name in
  fst @@ List.find (fun (_, field_) -> field = field_) sd.struct_fields

let rec type_has_K1K2 su_env ty =
  match ty with
  | Tint sec | Tfloat sec | Tbool sec ->
    sec <> Public K0Public
  | Tunit -> false
  | Tref _ -> false
  | Tarray (ty_elem, _, _) -> type_has_K1K2 su_env ty_elem
  | Tstruct st_name ->
    let st = find_struct su_env st_name in
    List.exists (fun (field_ty, _) -> type_has_K1K2 su_env field_ty) st.struct_fields

(* Symbolic AST ***************************************************************)

let string_of_array arr string_of_elem =
  "[" ^ Array.fold_left (fun text elem -> text ^ " " ^ string_of_elem elem) "" arr ^ "]"

type var_alias =
  (* AliasNorm (var, n) represents a normal variable [var] with a label [n].
     The label differentiates this variable from other occurrences during the execution. *)
  | AliasNorm of string * int
  (* AliasGlob var represents a global variable [var]. *)
  | AliasGlob of string

type value =
  | Vunit
  | Vint of int
  | Vfloat of float
  | Vbool of bool
  | Vref of lvalue_node
  | Vnull
  | Varray of value array
  | Vstruct of (string, value) Hashtbl.t
and lvalue =
  | Vvar of var_alias
  | Vindex of lvalue_node * seclvl * int
  | Vfield of lvalue_node * string
and lvalue_node = {
  lvalue : lvalue;
  lvalue_type : typ;
}

let mk_lvalue lv ty = {
  lvalue = lv;
  lvalue_type = ty;
}

type typed_value =
| TVunit
| TVint of seclvl * int
| TVfloat of seclvl * float
| TVbool of seclvl * bool
| TVref of lvalue_node
| TVnull
| TVarray of typ * seclvl * int * (typed_value array)
| TVstruct of typed_value StringMap.t

type sexpr_meta = {
  sexpr_type : typ;
  sexpr_loc : Location.t;
}
type slexpr_meta = {
  slexpr_type : typ;
  slexpr_loc : Location.t;
}

(* Note: There's no longer deref in slexpr, and all ref in sexpr are now
   pointing at an lvalue rather than an expression. *)
type sexpr =
  | SEunit
  | SEbool of bool
  | SEint of int
  | SEfloat of float
  | SEnull
  | SEref of lvalue_node
  | SElexpr of slexpr_node
  | SEarrayinit of seclvl * sexpr_node list
  | SEstructinit of (string * sexpr_node) list
  | SEbuiltin of string * sexpr_node list
and slexpr =
  | SEvar of var_alias
  | SEindex of slexpr_node * seclvl * sexpr_node
  | SEfield of slexpr_node * string
and sexpr_node = {
  sexpr : sexpr;
  sexpr_meta : sexpr_meta;
}
and slexpr_node = {
  slexpr : slexpr;
  slexpr_meta : slexpr_meta;
}

let mk_sexpr se ty loc = {
  sexpr = se;
  sexpr_meta = {
    sexpr_type = ty;
    sexpr_loc = loc
  }
}

let mk_slexpr sle ty loc = {
  slexpr = sle;
  slexpr_meta = {
    slexpr_type = ty;
    slexpr_loc = loc
  }
}

let type_of_sexpr se = se.sexpr_meta.sexpr_type
let type_of_slexpr sle = sle.slexpr_meta.slexpr_type
let type_of_lvalue lv = lv.lvalue_type

let loc_of_sexpr se = se.sexpr_meta.sexpr_loc
let loc_of_slexpr sle = sle.slexpr_meta.slexpr_loc

type scmd_meta = {
  scmd_loc : Location.t;
}
type scmd =
  | SCdef of typ * var_alias * sexpr_node
  | SCasgn of slexpr_node * sexpr_node
  | SCassert of sexpr_node
  | SCcall of typ * var_alias * string * sexpr_node list * (lvalue_node * value) list (*pubR*)
  | SCsandboxcall of typ * sandbox_anno_kind * var_alias * string * sexpr_node list
and scmd_node = {
  scmd : scmd;
  scmd_meta : scmd_meta;
}

let mk_scmd sc loc = {
  scmd = sc;
  scmd_meta = { scmd_loc = loc }
}

let loc_of_scmd sc = sc.scmd_meta.scmd_loc

type cmdinfo =
{
  cmdinfo_id : int; (* command id *)
  cmdinfo_cmd : scmd_node;
  cmdinfo_deps : (int * int * lvalue_node list) list; (* src command id, src chunk id, lvalues *)
  cmdinfo_defs : (int * int * lvalue_node list) list; (* dst command id, dst chunk id, lvalues *)
}

let is_global_alias = function
  | AliasGlob _ -> true
  | _ -> false

let string_of_alias = function
  | AliasNorm (var, n) ->
    var ^ "$" ^ string_of_int n
  | AliasGlob var -> var ^ "$g"

let name_of_alias = function
  | AliasNorm (var, _) -> var
  | AliasGlob var -> var

(** Find the base variable of an lvalue *)
let rec base_of_lvalue lv =
  match lv.lvalue with
  | Vvar alias -> type_of_lvalue lv, alias
  | Vindex (lv_arr, _, _) -> base_of_lvalue lv_arr
  | Vfield (lv_st, _) -> base_of_lvalue lv_st

(** Deep copy a value *)
let rec copy_value = function
  | Varray arr ->
    let arr' = Array.make (Array.length arr) Vunit in
    Array.iteri (fun i v -> Array.set arr' i (copy_value v)) arr;
    Varray arr'
  | Vstruct tbl ->
    let tbl' = Hashtbl.create (Hashtbl.length tbl) in
    Hashtbl.iter (fun field v -> Hashtbl.add tbl' field (copy_value v)) tbl;
    Vstruct tbl'
  | v -> v

let rec base_of_slexpr_node sle =
  match sle.slexpr with
  | SEvar alias -> type_of_slexpr sle, alias
  | SEindex (sle_arr, _, _) -> base_of_slexpr_node sle_arr
  | SEfield (sle_st, _) -> base_of_slexpr_node sle_st

let rec string_of_value = function
  | Vunit -> "tt"
  | Vint i -> string_of_int i
  | Vfloat f -> Printf.sprintf "%f" f
  | Vbool b -> string_of_bool b
  | Vref lv -> "& " ^ string_of_lvalue_node lv
  | Vnull -> "null"
  | Varray arr -> string_of_array arr string_of_value
  | Vstruct st ->
    let asgns = Hashtbl.fold (fun field v asgns' -> (field ^ " = " ^ string_of_value v) :: asgns') st [] in
    "{" ^ String.concat ", " asgns ^ "}"
and string_of_lvalue = function
  | Vvar var -> "("  ^ string_of_alias var ^ ")"
  | Vindex (arr, sec, index) -> string_of_lvalue_node arr ^ "[" ^ string_of_seclvl sec ^ " " ^ string_of_int index ^ "]"
  | Vfield (st, field) -> string_of_lvalue_node st ^ "." ^ field
and string_of_lvalue_node lv =
  string_of_lvalue lv.lvalue

and string_of_sexpr = function
  | SEunit -> "tt"
  | SEint i -> string_of_int i
  | SEfloat f -> Printf.sprintf "%f" f
  | SEbool b -> string_of_bool b
  | SEnull -> "null"
  | SEref lv -> "& " ^ string_of_lvalue_node lv
  | SElexpr le -> string_of_slexpr_node le
  | SEarrayinit (sec, se_inits) ->
    string_of_seclvl sec ^ " {" ^ String.concat ", " (List.map string_of_sexpr_node se_inits) ^ "}"
  | SEstructinit se_asgns -> "{" ^ String.concat ", " (List.map (fun (field, se) -> field ^ " = " ^ string_of_sexpr_node se) se_asgns) ^ "}"
  | SEbuiltin (f, args) -> f ^ "(" ^ String.concat ", " (List.map string_of_sexpr_node args) ^ ")"
and string_of_slexpr = function
  | SEvar alias -> string_of_alias alias
  | SEindex (arr, sec, index) -> string_of_slexpr_node arr ^ "[" ^ string_of_seclvl sec ^ " " ^ string_of_sexpr_node index ^ "]"
  | SEfield (st, field) -> string_of_slexpr_node st ^ "." ^ field
and string_of_sexpr_node e = string_of_sexpr e.sexpr
and string_of_slexpr_node le = string_of_slexpr le.slexpr

let string_of_scmd = function
  | SCdef (ty, alias, se_init) ->
    string_of_typ ty ^ " " ^ string_of_alias alias ^ " = " ^ string_of_sexpr_node se_init
  | SCasgn (sle, se) -> Printf.sprintf "%s = %s" (string_of_slexpr_node sle) (string_of_sexpr_node se)
  | SCassert se -> "assert " ^ string_of_sexpr_node se
  | SCcall (ty, alias, f, args, pubR) ->
    "sync " ^ String.concat ", " (List.map (fun (lv, v) -> string_of_lvalue_node lv ^ " = " ^ string_of_value v) pubR) ^
    " then " ^ string_of_typ ty ^ " " ^ string_of_alias alias ^ " = " ^
    f ^ "(" ^ String.concat ", " (List.map string_of_sexpr_node args) ^ ")"
  | SCsandboxcall (ty, _, alias, f, args) ->
    string_of_typ ty ^ " " ^ string_of_alias alias ^ " = " ^
    f ^ "(" ^ String.concat ", " (List.map string_of_sexpr_node args) ^ ")"
let string_of_scmd_node c = string_of_scmd c.scmd

let rec lvalue_of_slexpr sle =
  let ret raw_lv = Some (mk_lvalue raw_lv (type_of_slexpr sle)) in
  match sle.slexpr with
  | SEvar var -> ret (Vvar var)
  | SEindex (sle_arr, sec, se_index) ->
    begin match lvalue_of_slexpr sle_arr, se_index.sexpr with
    | Some lv_arr, SEint index -> ret (Vindex (lv_arr, sec, index))
    | _, _ -> None
    end
  | SEfield (sle_base, field) ->
    match lvalue_of_slexpr sle_base with
    | Some lv_base -> ret (Vfield (lv_base, field))
    | _ -> None

(* Return Some lvalue of K0 slexpr. May fail with None. *)
let rec lvalue_of_K0_slexpr sle =
  let ret raw_lv = Some (mk_lvalue raw_lv (type_of_slexpr sle)) in
  match sle.slexpr with
  | SEvar var -> ret (Vvar var)
  | SEindex (sle_arr, Public K0Public, se_index) ->
    begin match lvalue_of_K0_slexpr sle_arr, se_index.sexpr with
    | Some lv_arr, SEint index -> ret (Vindex (lv_arr, Public K0Public, index))
    | _, _ -> None
    end
  | SEindex _ -> None
  | SEfield (sle_base, field) ->
    match lvalue_of_K0_slexpr sle_base with
    | Some lv_base -> ret (Vfield (lv_base, field))
    | _ -> None

(* Return Some lvalue of K0/K1 slexpr. May fail with None. *)
let rec lvalue_of_K0K1_slexpr sle =
  let ret raw_lv = Some (mk_lvalue raw_lv (type_of_slexpr sle)) in
  match sle.slexpr with
  | SEvar var -> ret (Vvar var)
  | SEindex (sle_arr, sec, se_index) ->
    if seclvl_le sec (Plocal K1Plocal) then
      begin match lvalue_of_K0K1_slexpr sle_arr, se_index.sexpr with
      | Some lv_arr, SEint index -> ret (Vindex (lv_arr, sec, index))
      | _, _ -> None
      end
    else None
  | SEfield (sle_base, field) ->
    match lvalue_of_K0K1_slexpr sle_base with
    | Some lv_base -> ret (Vfield (lv_base, field))
    | _ -> None

(** Convert an slexpr at K0 to the closest and smallest lvalue. For example:
    arr[10].x becomes arr[10].x, arr[idx].x becomes arr, and st.f[idx] becomes st.f. *)
let rec closest_lvalue_of_slexpr sle =
  let ret raw_lv = mk_lvalue raw_lv (type_of_slexpr sle) in
  match sle.slexpr with
  | SEvar var -> ret (Vvar var)
  | SEindex (sle_arr, Public K0Public, se_index) ->
    begin match lvalue_of_slexpr sle_arr, se_index.sexpr with
    | Some lv_arr, SEint index -> ret (Vindex (lv_arr, Public K0Public, index))
    | _, _ -> raise (FatalInAST "SEindex of pub0 can not be fully evaluated")
    end
  | SEindex (sle_arr, _, _) -> closest_lvalue_of_slexpr sle_arr
  | SEfield (sle_st, field) ->
    match lvalue_of_slexpr sle_st with
    | Some lv_st -> ret (Vfield (lv_st, field))
    | _ -> closest_lvalue_of_slexpr sle_st

(** Convert lvalue to slexpr. Always succeed. *)
let rec slexpr_of_lvalue base_lv =
  let ret raw_sle = mk_slexpr raw_sle (type_of_lvalue base_lv) Location.none in
  match base_lv.lvalue with
  | Vvar var -> ret (SEvar var)
  | Vindex (lv, sec, index) ->
    let sle_arr = slexpr_of_lvalue lv in
    let k0_index = mk_sexpr (SEint index) (Tint (Public K0Public)) Location.none in
    let k1_index = mk_sexpr (SEbuiltin ("k1pub_int_of_k0", [k0_index])) (Tint (Public K1Public)) Location.none in
    let k2_index = mk_sexpr (SEbuiltin ("k2pub_int_of_k0", [k0_index])) (Tint (Public K2Public)) Location.none in
    let se_index = begin match sec with
    | Public K0Public -> k0_index
    | Public K1Public -> k1_index
    | Public K2Public -> k2_index
    | Private K1Private -> mk_sexpr (SEbuiltin ("k1pvt_int_of_pub", [k1_index])) (Tint sec) Location.none
    | Private K2Private -> mk_sexpr (SEbuiltin ("k2pvt_int_of_pub", [k2_index])) (Tint sec) Location.none
    | Plocal K1Plocal -> mk_sexpr (SEbuiltin ("k1plc_int_of_pub", [k1_index])) (Tint sec) Location.none
    | Plocal K2Plocal -> mk_sexpr (SEbuiltin ("k2plc_int_of_pub", [k2_index])) (Tint sec) Location.none
    end in
    ret (SEindex (sle_arr, sec, se_index))
  | Vfield (lv, field) ->
    let sle_st = slexpr_of_lvalue lv in
    ret (SEfield (sle_st, field))

(* Alias related constructions *)
module AliasHash =
  struct
    type t = var_alias
    let equal = (=)
    let hash alias = Hashtbl.hash (string_of_alias alias) (* TODO: avoid converting to string *)
  end

module AliasHashtbl = Hashtbl.Make(AliasHash)

module LValueHash =
  struct
    type t = lvalue_node
    let equal = (=)
    let hash lv = Hashtbl.hash (string_of_lvalue_node lv) (* TODO: avoid converting to string *)
  end

module LValueHashtbl = Hashtbl.Make(LValueHash)

module AliasOrdered =
struct
  type t = var_alias
  let compare a1 a2 =
    Stdlib.compare (string_of_alias a1) (string_of_alias a2)
end

module AliasSet = Set.Make(AliasOrdered)
module AliasMap = Map.Make(AliasOrdered)

module LValueOrdered =
struct
  type t = lvalue_node
  let compare v1 v2 =
    Stdlib.compare (string_of_lvalue_node v1) (string_of_lvalue_node v2) (* TODO: avoid converting to string *)
end

exception FatalInLValueTree of string

(** An immutable set of lvalues. Stored like octree to save space. *)
module LValueTree : sig
  type t
  val empty : t
  val is_empty : t -> bool
  val singleton : lvalue_node -> t
  val add : lvalue_node -> t -> t
  val union : t -> t -> t
  val diff : struct_union_env -> t -> t -> t
  val iter : struct_union_env -> (lvalue_node -> unit) -> t -> unit
  val aliases_seq : t -> (var_alias * typ) Seq.t
end
=
struct
  type lvalue_tree =
  | Leaf
  | Fields of lvalue_tree StringMap.t
  | Indexes of lvalue_tree IntMap.t

  type t = (typ * lvalue_tree) AliasMap.t

  let empty = AliasMap.empty

  let is_empty = AliasMap.is_empty

  type access_choice =
  | ACindex of int
  | ACfield of string

  let rec access_of_lvalue_node lv =
    match lv.lvalue with
    | Vvar alias -> (alias, type_of_lvalue lv, [])
    | Vindex (lv_arr, _, idx) ->
      let (alias, ty, path) = access_of_lvalue_node lv_arr in
      (alias, ty, path @ [ACindex idx])
    | Vfield (lv_st, field) ->
      let (alias, ty,  path) = access_of_lvalue_node lv_st in
      (alias, ty, path @ [ACfield field])

  let rec build_lvalue_tree = function
  | [] -> Leaf
  | ACindex idx :: path ->
    let subtree = build_lvalue_tree path in
    Indexes (IntMap.singleton idx subtree)
  | ACfield field :: path ->
    let subtree = build_lvalue_tree path in
    Fields (StringMap.singleton field subtree)

  let singleton lv =
    let (alias, ty, path) = access_of_lvalue_node lv in
    let subtree = build_lvalue_tree path in
    AliasMap.singleton alias (ty, subtree)

  type lookup_status =
  | Fail
  | Exact
  | Shorter
  | Longer

  let rec lookup_lvalue_tree tree = function
  | [] -> if tree = Leaf then Exact else Shorter
  | ACindex idx :: path ->
    begin match tree with
    | Leaf -> Longer
    | Fields _ -> raise (FatalInLValueTree "lookup index but entered Fields")
    | Indexes m ->
      match IntMap.find_opt idx m with
      | None -> Fail
      | Some subtree -> lookup_lvalue_tree subtree path
    end
  | ACfield field :: path ->
    begin match tree with
    | Leaf -> Longer
    | Indexes _ -> raise (FatalInLValueTree "lookup field but entered Indexes")
    | Fields m ->
      match StringMap.find_opt field m with
      | None -> Fail
      | Some subtree -> lookup_lvalue_tree subtree path
    end

  let lookup map lv =
    let (alias, _, path) = access_of_lvalue_node lv in
    match AliasMap.find_opt alias map with
    | None -> Fail
    | Some (_, tree) -> lookup_lvalue_tree tree path

  let rec add_to_lvalue_tree tree path =
    match path with
    | [] -> Leaf
    | ACindex idx :: path ->
      begin match tree with
      | Leaf -> Leaf (* the new path is part of an undivided node *)
      | Fields _ -> raise (FatalInLValueTree "add index but entered Fields")
      | Indexes map ->
        let update_strategy = function
        | None -> Some (build_lvalue_tree path)
        | Some subtree -> Some (add_to_lvalue_tree subtree path)
        in
        Indexes (IntMap.update idx update_strategy map)
      end
    | ACfield field :: path ->
      begin match tree with
      | Leaf -> Leaf (* the new path is part of an undivided node *)
      | Indexes _ -> raise (FatalInLValueTree "add field but entered Indexes")
      | Fields map ->
        let update_strategy = function
        | None -> Some (build_lvalue_tree path)
        | Some subtree -> Some (add_to_lvalue_tree subtree path)
        in
        Fields (StringMap.update field update_strategy map)
      end

  let add lv map =
    (* skip add if lv already exists in the map *)
    if lookup map lv = Exact then map
    else
      let (alias, ty, path) = access_of_lvalue_node lv in
      let update_strategy = function
      | None ->
        Some (ty, build_lvalue_tree path)
      | Some (ty, tree) -> Some (ty, add_to_lvalue_tree tree path)
      in
      AliasMap.update alias update_strategy map
  
  let rec iter_lvalue_tree_by_path f prefix = function
  | Leaf -> f prefix
  | Indexes map ->
    IntMap.iter (fun idx subtree ->
      iter_lvalue_tree_by_path f (prefix @ [ACindex idx]) subtree) map
  | Fields map ->
    StringMap.iter (fun field subtree ->
      iter_lvalue_tree_by_path f (prefix @ [ACfield field]) subtree) map

  let merge_lvalue_tree tree1 tree2 =
    let tree = ref tree1 in
    iter_lvalue_tree_by_path (fun path -> tree := add_to_lvalue_tree !tree path) [] tree2;
    !tree

  let union map1 map2 =
    let map = ref map1 in
    AliasMap.iter (fun alias (ty, tree2) ->
      map := AliasMap.update alias (function
      | None -> Some (ty, tree2)
      | Some (ty, tree1) -> Some (ty, merge_lvalue_tree tree1 tree2)) !map
    ) map2;
    !map
  
  (** Delete a path from a tree.
      Return None if the entire tree is deleted, or return Some new_tree.
      [ty] is the type of the tree. *)
  let rec remove_from_lvalue_tree su_env full_path tree ty =
    let delete_from_indexes idx path map =
      let update_strategy = function
      | None -> None (* idx does not exist in the tree *)
      | Some subtree -> (* either delete the entire subtree or replace with a new subtree *)
        remove_from_lvalue_tree su_env path subtree (type_of_element ty)
      in
      let new_map = IntMap.update idx update_strategy map in
      if IntMap.is_empty new_map then None
      else Some (Indexes new_map)
    in
    let delete_from_fields field path map =
      let update_strategy = function
      | None -> None (* field does not exist in the tree *)
      | Some subtree -> (* either delete the entire subtree or replace with a new subtree *)
        remove_from_lvalue_tree su_env path subtree (get_field_type su_env field)
      in
      let new_map = StringMap.update field update_strategy map in
      if StringMap.is_empty new_map then None
      else Some (Fields new_map)
    in
    match full_path with
    | [] -> None
    | ACindex idx :: path ->
      begin match tree with
      | Leaf -> (* unfold the array *)
        let size = array_size_from_type ty in
        let map = ref IntMap.empty in
        for i = 0 to size - 1 do
          map := IntMap.add i Leaf !map
        done;
        (* delete the path *)
        delete_from_indexes idx path !map
      | Fields _ -> raise (FatalInLValueTree "Remove index but entered Fields")
      | Indexes map ->
        delete_from_indexes idx path map
      end
    | ACfield field :: path ->
      begin match tree with
      | Leaf -> (* unfold the struct, ignore fields of only K0 info *)
        let st_name = find_field su_env field in
        let st = find_struct su_env st_name in
        let map = ref StringMap.empty in
        List.iter (fun (ty_field, field') ->
          if type_has_K1K2 su_env ty_field then
            map := StringMap.add field' Leaf !map
        ) st.struct_fields;
        (* delete the path *)
        delete_from_fields field path !map
      | Indexes _ -> raise (FatalInLValueTree "Remove field but entered Indexes")
      | Fields map ->
        delete_from_fields field path map
      end

  let diff_lvalue_tree su_env ty tree1 tree2 =
    let opt_tree = ref (Some tree1) in
    (* delete all tree2's paths *)
    iter_lvalue_tree_by_path (fun path ->
      match !opt_tree with
      | None -> () (* the entire tree is already deleted *)
      | Some tree ->
        opt_tree := remove_from_lvalue_tree su_env path tree ty
    ) [] tree2;
    !opt_tree

  let diff su_env (map1 : t) (map2 : t) : t =
    let map = ref map1 in
    AliasMap.iter (fun alias (_, tree2) ->
      map := AliasMap.update alias (function
      | None -> None
      | Some (ty, tree1) ->
        match diff_lvalue_tree su_env ty tree1 tree2 with
        | None -> None
        | Some new_tree -> Some (ty, new_tree)) !map
    ) map2;
    !map

  let rec iter_lvalue_tree su_env (f: lvalue_node -> unit) lv_base = function
  | Leaf -> f lv_base
  | Indexes map ->
    let ty_elem, sec = match type_of_lvalue lv_base with
    | Tarray (ty_elem, sec, _) -> ty_elem, sec
    | _ -> raise (FatalInLValueTree "Iterate indexes with non-array type")
    in
    IntMap.iter (fun idx subtree ->
      let lv_elem = mk_lvalue (Vindex (lv_base, sec, idx)) ty_elem in
      iter_lvalue_tree su_env f lv_elem subtree
    ) map
  | Fields map ->
    StringMap.iter (fun field subtree ->
      let ty_field = get_field_type su_env field in
      let lv_field = mk_lvalue (Vfield (lv_base, field)) ty_field in
      iter_lvalue_tree su_env f lv_field subtree
    ) map

  let iter su_env (f : lvalue_node -> unit) (map : t) =
    AliasMap.iter (fun alias (ty, tree) ->
      let lv_base = mk_lvalue (Vvar alias) ty in
      iter_lvalue_tree su_env f lv_base tree
    ) map

  let aliases_seq (map: t) =
    Seq.map (fun (alias, (ty, _)) -> (alias, ty)) (AliasMap.to_seq map)
end

let _debug_lvaluetree su_env tree =
  LValueTree.iter su_env (fun lv ->
    Logs.debug (fun m -> m "%s" (string_of_lvalue_node lv))
  ) tree

(* module LValueSet = Set.Make(LValueOrdered) *)
module LValueMap = Map.Make(LValueOrdered)
(*
let _debug_lvalueset s =
  LValueSet.iter (fun lv -> logs_debug_endline @@ ">> " ^ string_of_lvalue_node lv) s

(** Convert an lvalue set into a list of lvalues. *)
let list_of_lvalueset s =
  let res = ref [] in
  LValueSet.iter (fun lv -> res := lv :: !res) s;
  !res

(** Union multiple lvalue sets. *)
let lvalueset_unions lst =
  let res = ref LValueSet.empty in
  List.iter (fun set -> res := LValueSet.union set !res) lst;
  !res
*)
let lvaluetree_unions lst =
  let res = ref LValueTree.empty in
  List.iter (fun tree -> res := LValueTree.union tree !res) lst;
  !res

(* atomic call environment *********************************************** *)

exception UndefinedAtomcall of var_alias
exception RedefinedAtomcall of var_alias

type liveinfo =
  {
    liveinfo_K1K2_R : LValueTree.t;
    liveinfo_K1K2_W : LValueTree.t;
  }

type atomic_call_env = liveinfo AliasHashtbl.t

let atomcall_info (env: atomic_call_env) alias =
    try AliasHashtbl.find env alias
    with Not_found -> raise (UndefinedAtomcall alias)

let atomcall_record (env: atomic_call_env) alias info =
  if AliasHashtbl.mem env alias then
    raise (RedefinedAtomcall alias)
  else
    AliasHashtbl.add env alias info

type ou_chunk =
{
  chunk_pvt_in : lvalue_node list;
  chunk_prog : scmd_node list;
}

type ou_block =
{
  block_deps : LValueTree.t;
  block_cmd_ids : int list;
}