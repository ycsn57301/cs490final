open Ast

val ssim_prog : gvardef_node list -> fundef_node list -> (string, funsig) Hashtbl.t -> struct_union_env -> (scmd_node * int) Array.t * atomic_call_env