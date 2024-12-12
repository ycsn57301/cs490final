open Ast

val builtin_types : (string, funsig) Hashtbl.t
val builtin_costs : (string, int) Hashtbl.t
(* val builtin_pub_funs : (string, value list -> value) Hashtbl.t *)
(* val builtin_funs : (string, sexpr list -> sexpr) Hashtbl.t *)
(* val builtin_pub_fun : string -> value list -> value *)
(* val builtin_fun : string -> sexpr_node list -> sexpr *)
val ssim_builtin : string -> sexpr_node list -> sexpr
val dsim_builtin : string -> sexpr_node list -> sexpr