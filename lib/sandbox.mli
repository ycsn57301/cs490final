open Ast

val check_sandbox : struct_union_env -> (string, funsig) Hashtbl.t -> fundef -> unit