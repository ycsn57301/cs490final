open Ast
open Analysis
(*
val eval_edge_vars : fundef_node list -> gvardef_node list -> struct_union_env -> ou_chunk list ->
    ((lvalue_node * expr_node) list) list
*)
val dsim_prog : fundef_node list -> struct_union_env -> scmd_node array -> depnode array -> typed_value LValueHashtbl.t array