open Ast

exception FatalInBuiltin of string
(* exception ArgIsNotValue of sexpr_node *)

(* Meta info ********************************************************)

(** Return value is pvt *)
let pvt_funs_meta =
  let homo_funs_pattern =
    [
      (* int *)
      "int_add", ([functor_Tint; functor_Tint], functor_Tint), 32;
      "int_mul", ([functor_Tint; functor_Tint], functor_Tint), 997;
      "int_sub", ([functor_Tint; functor_Tint], functor_Tint), 32;
      "int_div", ([functor_Tint; functor_Tint], functor_Tint), 10000; (* unsure *)
      "int_mod", ([functor_Tint; functor_Tint], functor_Tint), 10000; (* unsure *)
      "int_lor", ([functor_Tint; functor_Tint], functor_Tint), 32;
      "int_lsl", ([functor_Tint; functor_Tint], functor_Tint), 5; (* unsure *)
      "int_lsr", ([functor_Tint; functor_Tint], functor_Tint), 5; (* unsure *)
      "int_land", ([functor_Tint; functor_Tint], functor_Tint), 32;
      "int_lxor", ([functor_Tint; functor_Tint], functor_Tint), 32;
      "int_ge", ([functor_Tint; functor_Tint], functor_Tbool), 32;
      "int_gt", ([functor_Tint; functor_Tint], functor_Tbool), 32;
      "int_le", ([functor_Tint; functor_Tint], functor_Tbool), 32;
      "int_lt", ([functor_Tint; functor_Tint], functor_Tbool), 32;
      "int_eq", ([functor_Tint; functor_Tint], functor_Tbool), 32;
      "int_ne", ([functor_Tint; functor_Tint], functor_Tbool), 32;
      "int_lnot", ([functor_Tint; functor_Tint], functor_Tbool), 32;
      "int_neg", ([functor_Tint; functor_Tint], functor_Tbool), 32;

      (* float *)
      (* reference of cost: https://github.com/emp-toolkit/emp-tool/tree/master/emp-tool/circuits *)
      "float_add", ([functor_Tfloat; functor_Tfloat], functor_Tfloat), 9824;
      "float_mul", ([functor_Tfloat; functor_Tfloat], functor_Tfloat), 35416;
      "float_sub", ([functor_Tfloat; functor_Tfloat], functor_Tfloat), 9824;
      "float_div", ([functor_Tfloat; functor_Tfloat], functor_Tfloat), 42612;
      "float_ge", ([functor_Tfloat; functor_Tfloat], functor_Tbool), 1788;
      "float_gt", ([functor_Tfloat; functor_Tfloat], functor_Tbool), 3560; (* unsure *)
      "float_le", ([functor_Tfloat; functor_Tfloat], functor_Tbool), 1788;
      "float_lt", ([functor_Tfloat; functor_Tfloat], functor_Tbool), 3560; (* unsure *)
      "float_eq", ([functor_Tfloat; functor_Tfloat], functor_Tbool), 1772;
      "float_ne", ([functor_Tfloat; functor_Tfloat], functor_Tbool), 1772;
      "float_neg", ([functor_Tfloat], functor_Tfloat), 32;

      (* bool *)
      "bool_and", ([functor_Tbool; functor_Tbool], functor_Tbool), 1;
      "bool_or", ([functor_Tbool; functor_Tbool], functor_Tbool), 1;
      "bool_eq", ([functor_Tbool; functor_Tbool], functor_Tbool), 1;
      "bool_ne", ([functor_Tbool; functor_Tbool], functor_Tbool), 1;
      "bool_not", ([functor_Tbool], functor_Tbool), 1;

      (* math functions *)
      "ceil", ([functor_Tfloat], functor_Tint), -1; (* unsupported *)
      "floor", ([functor_Tfloat], functor_Tint), -1; (* unsupported *)
      "round", ([functor_Tfloat], functor_Tint), -1; (* unsupported *)
      "cos", ([functor_Tfloat], functor_Tfloat), 37684;
      "sin", ([functor_Tfloat], functor_Tfloat), 37588;
      "tan", ([functor_Tfloat], functor_Tfloat), 37684 + 37588 + 42612;
      "log", ([functor_Tfloat], functor_Tfloat), 71056;
      "exp", ([functor_Tfloat], functor_Tfloat), 78648;
      (* TODO: add exp2, log2 *)
    ]
  in
  let hetero_funs_meta =
    [
      (* int *)
      "k1pvt_int_lsl_pub", ([Tint pvt1, CCval; Tint pub1, CCval], Tint pvt1), 5;
      "k2pvt_int_lsl_pub", ([Tint pvt2, CCval; Tint pub2, CCval], Tint pvt2), 5;
      "k1pvt_int_lsr_pub", ([Tint pvt1, CCval; Tint pub1, CCval], Tint pvt1), 5;
      "k2pvt_int_lsr_pub", ([Tint pvt2, CCval; Tint pub2, CCval], Tint pvt2), 5;

      (* cast *)
      (* "k1pvt_float_of_int", ([Tint pvt1], Tfloat pvt1), -1; (* unsupported *) *)
      "k1pvt_int_of_pub", ([Tint pub1, CCval], Tint pvt1), 32;
      "k2pvt_int_of_pub", ([Tint pub2, CCval], Tint pvt2), 32;
      "k2pvt_int_of_k1", ([Tint pvt2, CCval], Tint pvt1), 0;
      "k1pvt_int_of_plc", ([Tint plc1, CCval], Tint pvt1), 32;
      "k2pvt_int_of_plc", ([Tint plc2, CCval], Tint pvt2), 32;

      "k1pvt_float_of_pub", ([Tfloat pub1, CCval], Tfloat pvt1), 32;
      "k2pvt_float_of_pub", ([Tfloat pub2, CCval], Tfloat pvt2), 32;
      "k2pvt_float_of_k1", ([Tfloat pvt2, CCval], Tfloat pvt1), 0;
      "k1pvt_float_of_plc", ([Tfloat plc1, CCval], Tfloat pvt1), 32;
      "k2pvt_float_of_plc", ([Tfloat plc2, CCval], Tfloat pvt2), 32;

      "k1pvt_bool_of_pub", ([Tbool pvt1, CCval], Tbool pvt1), 32;
      "k2pvt_bool_of_pub", ([Tbool pub2, CCval], Tbool pvt2), 32;
      "k2pvt_bool_of_k1", ([Tbool pvt2, CCval], Tbool pvt1), 0;
      "k1pvt_bool_of_plc", ([Tbool plc1, CCval], Tbool pvt1), 32;
      "k2pvt_bool_of_plc", ([Tbool plc2, CCval], Tbool pvt2), 32;
    ]
  in
  let homo_funs_meta = List.concat_map (fun (suffix, (args_pattern, res_pattern), cost) ->
    let pvt1_sig = List.map (fun pattern -> pattern pvt1, CCval) args_pattern, res_pattern pvt1 in
    let pvt2_sig = List.map (fun pattern -> pattern pvt2, CCval) args_pattern, res_pattern pvt2 in
    [ "k1pvt_"^suffix, pvt1_sig, cost;
      "k2pvt_"^suffix, pvt2_sig, cost
    ]) homo_funs_pattern
  in
  homo_funs_meta @ hetero_funs_meta

(** Return value is pub *)
let pub_funs_meta =
  let homo_funs_pattern =
    [
      (* int *)
      "int_add", ([functor_Tint; functor_Tint], functor_Tint);
      "int_mul", ([functor_Tint; functor_Tint], functor_Tint);
      "int_sub", ([functor_Tint; functor_Tint], functor_Tint);
      "int_div", ([functor_Tint; functor_Tint], functor_Tint);
      "int_mod", ([functor_Tint; functor_Tint], functor_Tint);
      "int_lor", ([functor_Tint; functor_Tint], functor_Tint);
      "int_lsl", ([functor_Tint; functor_Tint], functor_Tint);
      "int_lsr", ([functor_Tint; functor_Tint], functor_Tint);
      "int_land", ([functor_Tint; functor_Tint], functor_Tint);
      "int_lxor", ([functor_Tint; functor_Tint], functor_Tint);
      "int_ge", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_gt", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_le", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_lt", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_eq", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_ne", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_lnot", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_neg", ([functor_Tint; functor_Tint], functor_Tbool);

      (* float *)
      (* reference of cost: https://github.com/emp-toolkit/emp-tool/tree/master/emp-tool/circuits *)
      "float_add", ([functor_Tfloat; functor_Tfloat], functor_Tfloat);
      "float_mul", ([functor_Tfloat; functor_Tfloat], functor_Tfloat);
      "float_sub", ([functor_Tfloat; functor_Tfloat], functor_Tfloat);
      "float_div", ([functor_Tfloat; functor_Tfloat], functor_Tfloat);
      "float_ge", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_gt", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_le", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_lt", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_eq", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_ne", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_neg", ([functor_Tfloat], functor_Tfloat);

      (* bool *)
      "bool_and", ([functor_Tbool; functor_Tbool], functor_Tbool);
      "bool_or", ([functor_Tbool; functor_Tbool], functor_Tbool);
      "bool_eq", ([functor_Tbool; functor_Tbool], functor_Tbool);
      "bool_ne", ([functor_Tbool; functor_Tbool], functor_Tbool);
      "bool_not", ([functor_Tbool], functor_Tbool);

      (* math functions *)
      "ceil", ([functor_Tfloat], functor_Tint);
      "floor", ([functor_Tfloat], functor_Tint);
      "round", ([functor_Tfloat], functor_Tint);
      "cos", ([functor_Tfloat], functor_Tfloat);
      "sin", ([functor_Tfloat], functor_Tfloat);
      "tan", ([functor_Tfloat], functor_Tfloat);
      "log", ([functor_Tfloat], functor_Tfloat);
      "exp", ([functor_Tfloat], functor_Tfloat);
      (* TODO: add exp2, log2 *)
    ]
  in
  let hetero_funs_meta =
    [
      "pi", ([], Tfloat pub0), 0;
      "verifier_rand", ([Tint pub2, CCval; Tint pub2, CCval], Tint pub2), 32; (* unsure *)

      (* cast *)
      "k0pub_float_of_int", ([Tint pub0, CCval], Tfloat pub0), 0;
      "k1pub_float_of_int", ([Tint pub1, CCval], Tfloat pub1), 0;
      "k2pub_float_of_int", ([Tint pub2, CCval], Tfloat pub2), 0;

      "k1pub_int_of_pvt", ([Tint pvt1, CCval], Tint pub1), 32;
      "k2pub_int_of_pvt", ([Tint pvt2, CCval], Tint pub2), 32;
      "k1pub_int_of_k0", ([Tint pub0, CCval], Tint pub1), 0;
      "k2pub_int_of_k1", ([Tint pub1, CCval], Tint pub2), 0;
      "k2pub_int_of_k0", ([Tint pub0, CCval], Tint pub2), 0;

      "k1pub_float_of_pvt", ([Tfloat pvt1, CCval], Tfloat pub1), 32;
      "k2pub_float_of_pvt", ([Tfloat pvt2, CCval], Tfloat pub2), 32;
      "k1pub_float_of_k0", ([Tfloat pub0, CCval], Tfloat pub1), 0;
      "k2pub_float_of_k1", ([Tfloat pub1, CCval], Tfloat pub2), 0;
      "k2pub_float_of_k0", ([Tfloat pub0, CCval], Tfloat pub2), 0;

      "k1pub_bool_of_pvt", ([Tbool pvt1, CCval], Tbool pub1), 32;
      "k2pub_bool_of_pvt", ([Tbool pvt2, CCval], Tbool pub2), 32;
      "k1pub_bool_of_k0", ([Tbool pub0, CCval], Tbool pub1), 0;
      "k2pub_bool_of_k1", ([Tbool pub1, CCval], Tbool pub2), 0;
      "k2pub_bool_of_k0", ([Tbool pub0, CCval], Tbool pub2), 0;

      "k0pub_int_print", ([Tint pub0, CCval], Tunit), 0;
      "k1pub_int_print", ([Tint pub1, CCval], Tunit), 0;
      "k2pub_int_print", ([Tint pub2, CCval], Tunit), 0;

      "k0pub_float_print", ([Tfloat pub0, CCval], Tunit), 0;
      "k1pub_float_print", ([Tfloat pub1, CCval], Tunit), 0;
      "k2pub_float_print", ([Tfloat pub2, CCval], Tunit), 0;

      "k0pub_bool_print", ([Tbool pub0, CCval], Tunit), 0;
      "k1pub_bool_print", ([Tbool pub1, CCval], Tunit), 0;
      "k2pub_bool_print", ([Tbool pub2, CCval], Tunit), 0;

      "k0pub_int_debug0", ([Tint pub0, CCval], Tunit), 0;
      "k0pub_int_debug1", ([Tint pub0, CCval], Tunit), 0;
      "k1pub_int_debug1", ([Tint pub1, CCval], Tunit), 0;

      "k0pub_float_debug0", ([Tfloat pub0, CCval], Tunit), 0;
      "k0pub_float_debug1", ([Tfloat pub0, CCval], Tunit), 0;
      "k1pub_float_debug1", ([Tfloat pub1, CCval], Tunit), 0;

      "k0pub_bool_debug0", ([Tbool pub0, CCval], Tunit), 0;
      "k0pub_bool_debug1", ([Tbool pub0, CCval], Tunit), 0;
      "k1pub_bool_debug1", ([Tbool pub1, CCval], Tunit), 0;
    ]
  in
  let homo_funs_meta = List.concat_map (fun (suffix, (args_pattern, res_pattern)) ->
    let pub0_sig = List.map (fun pattern -> pattern pub0, CCval) args_pattern, res_pattern pub0 in
    let pub1_sig = List.map (fun pattern -> pattern pub1, CCval) args_pattern, res_pattern pub1 in
    let pub2_sig = List.map (fun pattern -> pattern pub2, CCval) args_pattern, res_pattern pub2 in
    [ "k0pub_"^suffix, pub0_sig, 0;
      "k1pub_"^suffix, pub1_sig, 0;
      "k2pub_"^suffix, pub2_sig, 0
    ]) homo_funs_pattern
  in
  homo_funs_meta @ hetero_funs_meta

(** Return value is pub *)
let plc_funs_meta =
  let homo_funs_pattern =
    [
      (* int *)
      "int_add", ([functor_Tint; functor_Tint], functor_Tint);
      "int_mul", ([functor_Tint; functor_Tint], functor_Tint);
      "int_sub", ([functor_Tint; functor_Tint], functor_Tint);
      "int_div", ([functor_Tint; functor_Tint], functor_Tint);
      "int_mod", ([functor_Tint; functor_Tint], functor_Tint);
      "int_lor", ([functor_Tint; functor_Tint], functor_Tint);
      "int_lsl", ([functor_Tint; functor_Tint], functor_Tint);
      "int_lsr", ([functor_Tint; functor_Tint], functor_Tint);
      "int_land", ([functor_Tint; functor_Tint], functor_Tint);
      "int_lxor", ([functor_Tint; functor_Tint], functor_Tint);
      "int_ge", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_gt", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_le", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_lt", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_eq", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_ne", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_lnot", ([functor_Tint; functor_Tint], functor_Tbool);
      "int_neg", ([functor_Tint; functor_Tint], functor_Tbool);

      (* float *)
      (* reference of cost: https://github.com/emp-toolkit/emp-tool/tree/master/emp-tool/circuits *)
      "float_add", ([functor_Tfloat; functor_Tfloat], functor_Tfloat);
      "float_mul", ([functor_Tfloat; functor_Tfloat], functor_Tfloat);
      "float_sub", ([functor_Tfloat; functor_Tfloat], functor_Tfloat);
      "float_div", ([functor_Tfloat; functor_Tfloat], functor_Tfloat);
      "float_ge", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_gt", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_le", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_lt", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_eq", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_ne", ([functor_Tfloat; functor_Tfloat], functor_Tbool);
      "float_neg", ([functor_Tfloat], functor_Tfloat);

      (* bool *)
      "bool_and", ([functor_Tbool; functor_Tbool], functor_Tbool);
      "bool_or", ([functor_Tbool; functor_Tbool], functor_Tbool);
      "bool_eq", ([functor_Tbool; functor_Tbool], functor_Tbool);
      "bool_ne", ([functor_Tbool; functor_Tbool], functor_Tbool);
      "bool_not", ([functor_Tbool], functor_Tbool);

      (* math functions *)
      "ceil", ([functor_Tfloat], functor_Tint);
      "floor", ([functor_Tfloat], functor_Tint);
      "round", ([functor_Tfloat], functor_Tint);
      "cos", ([functor_Tfloat], functor_Tfloat);
      "sin", ([functor_Tfloat], functor_Tfloat);
      "tan", ([functor_Tfloat], functor_Tfloat);
      "log", ([functor_Tfloat], functor_Tfloat);
      "exp", ([functor_Tfloat], functor_Tfloat);
      (* TODO: add exp2, log2 *)
    ]
  in
  let hetero_funs_meta =
    [
      "prover_rand", ([Tint plc2, CCval; Tint plc2, CCval], Tint plc2), 32; (* unsure *)

      (* cast *)
      "k1plc_float_of_int", ([Tint plc1, CCval], Tfloat plc1), 0;
      "k2plc_float_of_int", ([Tint plc2, CCval], Tfloat plc2), 0;

      "k1plc_int_of_pvt", ([Tint pvt1, CCval], Tint plc1), 32; (* unsure *)
      "k2plc_int_of_pvt", ([Tint pvt2, CCval], Tint plc2), 32;
      "k2plc_int_of_k1", ([Tint plc1, CCval], Tint plc2), 0;
      "k1plc_int_of_pub", ([Tint pub1, CCval], Tint plc1), 0;
      "k2plc_int_of_pub", ([Tint pub2, CCval], Tint plc2), 0;

      "k1plc_float_of_pvt", ([Tfloat pvt1, CCval], Tfloat plc1), 32;
      "k2plc_float_of_pvt", ([Tfloat pvt2, CCval], Tfloat plc2), 32;
      "k2plc_float_of_k1", ([Tfloat plc1, CCval], Tfloat plc2), 0;
      "k1plc_float_of_pub", ([Tfloat pub1, CCval], Tfloat plc1), 0;
      "k2plc_float_of_pub", ([Tfloat pub2, CCval], Tfloat plc2), 0;

      "k1plc_bool_of_pvt", ([Tbool pvt1, CCval], Tbool plc1), 32;
      "k2plc_bool_of_pvt", ([Tbool pvt2, CCval], Tbool plc2), 32;
      "k2plc_bool_of_k1", ([Tbool plc1, CCval], Tbool plc2), 0;
      "k1plc_bool_of_pub", ([Tbool pub1, CCval], Tbool plc1), 0;
      "k2plc_bool_of_pub", ([Tbool pub2, CCval], Tbool plc2), 0;

      "k1plc_int_print", ([Tint plc1, CCval], Tunit), 0;
      "k2plc_int_print", ([Tint plc2, CCval], Tunit), 0;

      "k1plc_float_print", ([Tfloat plc1, CCval], Tunit), 0;
      "k2plc_float_print", ([Tfloat plc2, CCval], Tunit), 0;

      "k1plc_bool_print", ([Tbool plc1, CCval], Tunit), 0;
      "k2plc_bool_print", ([Tbool plc2, CCval], Tunit), 0;

      "k1plc_int_debug1", ([Tint plc1, CCval], Tunit), 0;
      "k1plc_float_debug1", ([Tfloat plc1, CCval], Tunit), 0;
      "k1plc_bool_debug1", ([Tbool plc1, CCval], Tunit), 0;
    ]
  in
  let homo_funs_meta = List.concat_map (fun (suffix, (args_pattern, res_pattern)) ->
    let plc1_sig = List.map (fun pattern -> pattern plc1, CCval) args_pattern, res_pattern plc1 in
    let plc2_sig = List.map (fun pattern -> pattern plc2, CCval) args_pattern, res_pattern plc2 in
    [ "k1plc_"^suffix, plc1_sig, 0;
      "k2plc_"^suffix, plc2_sig, 0
    ]) homo_funs_pattern
  in
  homo_funs_meta @ hetero_funs_meta

let builtin_meta = pvt_funs_meta @ pub_funs_meta @ plc_funs_meta

let builtin_types = Hashtbl.of_seq (List.to_seq (List.map (fun (f, f_sig, _) ->
  f, {
    funsig_params = fst f_sig;
    funsig_return = snd f_sig;
    funsig_anno = ATOMIC }) builtin_meta))

let builtin_costs = Hashtbl.of_seq (List.to_seq (List.map (fun (f, _, f_cost) -> (f, f_cost)) builtin_meta))

(* Evaluation ********************************************************)
(*
let builtin_nonpub_wrapper f =
  f, fun se -> SEbuiltin (f, se)

let builtin_public_wrapper impl se_args =
  let args = List.map (fun se ->
    match se.sexpr with
    | SEvalue v -> v
    | _ -> raise (ArgIsNotValue se)) se_args in
  SEvalue (impl args)
*)

exception NonatomSExpr of sexpr_node
exception NonatomValue of value
let atomic_value_of_sexpr base_se =
  match base_se.sexpr with
  | SEunit -> Vunit
  | SEint i -> Vint i
  | SEfloat f -> Vfloat f
  | SEbool b -> Vbool b
  | SEnull -> Vnull
  | _->
    raise (NonatomSExpr base_se)

let sexpr_of_atomic_value v =
  match v with
  | Vunit -> SEunit
  | Vint i -> SEint i
  | Vfloat f -> SEfloat f
  | Vbool b -> SEbool b
  | Vnull -> SEnull
  | _ -> raise (NonatomValue v)

let builtin_wrapper impl se_args =
  let args = List.map atomic_value_of_sexpr se_args in
  let res = impl args in
  sexpr_of_atomic_value res

(* int arithmatic *)
let builtin_int_add = function
  | [Vint i1; Vint i2] -> Vint (i1 + i2)
  | _ -> raise (FatalInBuiltin "pub_int_add")

let builtin_int_sub = function
  | [Vint i1; Vint i2] -> Vint (i1 - i2)
  | _ -> raise (FatalInBuiltin "pub_int_sub")

let builtin_int_mul = function
  | [Vint i1; Vint i2] -> Vint (i1 * i2)
  | _ -> raise (FatalInBuiltin "pub_int_mul")

let builtin_int_div = function
  | [Vint i1; Vint i2] -> Vint (i1 / i2)
  | _ -> raise (FatalInBuiltin "pub_int_div")

let builtin_int_mod = function
  | [Vint i1; Vint i2] -> Vint (i1 mod i2)
  | _ -> raise (FatalInBuiltin "pub_int_mod")

let builtin_int_lor = function
  | [Vint i1; Vint i2] -> Vint (i1 lor i2)
  | _ -> raise (FatalInBuiltin "pub_int_lor")

let builtin_int_lsl = function
  | [Vint i1; Vint i2] -> Vint ((i1 lsl i2) land 0xffffffff)
  | _ -> raise (FatalInBuiltin "pub_int_lsl")

let builtin_int_lsr = function
  | [Vint i1; Vint i2] -> Vint (i1 lsr i2)
  | _ -> raise (FatalInBuiltin "pub_int_lsr")

let builtin_int_land = function
  | [Vint i1; Vint i2] -> Vint (i1 land i2)
  | _ -> raise (FatalInBuiltin "pub_int_land")

let builtin_int_lxor = function
  | [Vint i1; Vint i2] -> Vint (i1 lxor i2)
  | _ -> raise (FatalInBuiltin "pub_int_lxor")

let builtin_int_ge = function
  | [Vint i1; Vint i2] -> Vbool (i1 >= i2)
  | _ -> raise (FatalInBuiltin "pub_int_ge")

let builtin_int_gt = function
  | [Vint i1; Vint i2] -> Vbool (i1 > i2)
  | _ -> raise (FatalInBuiltin "pub_int_gt")

let builtin_int_le = function
  | [Vint i1; Vint i2] -> Vbool (i1 <= i2)
  | _ -> raise (FatalInBuiltin "pub_int_le")

let builtin_int_lt = function
  | [Vint i1; Vint i2] -> Vbool (i1 < i2)
  | _ -> raise (FatalInBuiltin "pub_int_lt")

let builtin_int_eq = function
  | [Vint i1; Vint i2] -> Vbool (i1 = i2)
  | _ -> raise (FatalInBuiltin "pub_int_eq")

let builtin_int_ne = function
  | [Vint i1; Vint i2] -> Vbool (i1 <> i2)
  | _ -> raise (FatalInBuiltin "pub_int_ne")

let builtin_int_lnot = function
  | [Vint i1] -> Vint (lnot i1)
  | _ -> raise (FatalInBuiltin "pub_int_lnot")

let builtin_int_neg = function
  | [Vint i1] -> Vint (- i1)
  | _ -> raise (FatalInBuiltin "pub_int_neg")

(* float arithmatic *)
let builtin_float_add = function
  | [Vfloat f1; Vfloat f2] -> Vfloat (f1 +. f2)
  | _ -> raise (FatalInBuiltin "pub_float_add")

let builtin_float_sub = function
  | [Vfloat f1; Vfloat f2] -> Vfloat (f1 -. f2)
  | _ -> raise (FatalInBuiltin "pub_float_sub")

let builtin_float_mul = function
  | [Vfloat f1; Vfloat f2] -> Vfloat (f1 *. f2)
  | _ -> raise (FatalInBuiltin "pub_float_mul")

let builtin_float_div = function
  | [Vfloat f1; Vfloat f2] -> Vfloat (f1 /. f2)
  | _ -> raise (FatalInBuiltin "pub_float_div")

let builtin_float_ge = function
  | [Vfloat f1; Vfloat f2] -> Vbool (f1 >= f2)
  | _ -> raise (FatalInBuiltin "pub_float_ge")

let builtin_float_gt = function
  | [Vfloat f1; Vfloat f2] -> Vbool (f1 > f2)
  | _ -> raise (FatalInBuiltin "pub_float_gt")

let builtin_float_le = function
  | [Vfloat f1; Vfloat f2] -> Vbool (f1 <= f2)
  | _ -> raise (FatalInBuiltin "pub_float_le")

let builtin_float_lt = function
  | [Vfloat f1; Vfloat f2] -> Vbool (f1 < f2)
  | _ -> raise (FatalInBuiltin "pub_float_lt")

let builtin_float_eq = function
  | [Vfloat f1; Vfloat f2] -> Vbool (f1 = f2)
  | _ -> raise (FatalInBuiltin "pub_float_eq")

let builtin_float_ne = function
  | [Vfloat f1; Vfloat f2] -> Vbool (f1 <> f2)
  | _ -> raise (FatalInBuiltin "pub_float_ne")

let builtin_float_neg = function
  | [Vfloat f1] -> Vfloat (-. f1)
  | _ -> raise (FatalInBuiltin "pub_float_neg")

(* bool arithmatic *)
let builtin_bool_and = function
  | [Vbool b1; Vbool b2] -> Vbool (b1 && b2)
  | _ -> raise (FatalInBuiltin "pub_bool_and")

let builtin_bool_or = function
  | [Vbool b1; Vbool b2] -> Vbool (b1 || b2)
  | _ -> raise (FatalInBuiltin "pub_bool_or")

let builtin_bool_eq = function
  | [Vbool b1; Vbool b2] -> Vbool (b1 = b2)
  | _ -> raise (FatalInBuiltin "pub_bool_eq")

let builtin_bool_ne = function
  | [Vbool b1; Vbool b2] -> Vbool (b1 <> b2)
  | _ -> raise (FatalInBuiltin "pub_bool_ne")

let builtin_bool_not = function
  | [Vbool b1] -> Vbool (not b1)
  | _ -> raise (FatalInBuiltin "pub_bool_not")

(* math functions *)
let builtin_ceil = function
  | [Vfloat f] -> Vint (Float.to_int (Float.ceil f))
  | _ -> raise (FatalInBuiltin "pub_ceil")

let builtin_floor = function
  | [Vfloat f] -> Vint (Float.to_int (Float.floor f))
  | _ -> raise (FatalInBuiltin "pub_floor")

let builtin_round = function
  | [Vfloat f] -> Vint (Float.to_int (Float.round f))
  | _ -> raise (FatalInBuiltin "pub_floor")

let builtin_cos = function
  | [Vfloat f] -> Vfloat (Float.cos f)
  | _ -> raise (FatalInBuiltin "pub_cos")

let builtin_sin = function
  | [Vfloat f] -> Vfloat (Float.sin f)
  | _ -> raise (FatalInBuiltin "pub_sin")

let builtin_tan = function
  | [Vfloat f] -> Vfloat (Float.tan f)
  | _ -> raise (FatalInBuiltin "pub_tan")

let builtin_pi = function
  | [] -> Vfloat Float.pi
  | _ -> raise (FatalInBuiltin "pi")

let builtin_log = function
  | [Vfloat f] -> Vfloat (Float.log f)
  | _ -> raise (FatalInBuiltin "log")

let builtin_exp = function
  | [Vfloat f] -> Vfloat (Float.exp f)
  | _ -> raise (FatalInBuiltin "exp")

(* type cast *)
let builtin_float_of_int = function
  | [Vint i] -> Vfloat (Float.of_int i)
  | _ -> raise (FatalInBuiltin "pub_float_of_int")

let builtin_id = function
  | [v] -> v
  | _ ->raise (FatalInBuiltin "id")

(* debug *)
let builtin_debug_int = function
  | [Vint i] -> print_endline (string_of_int i); Vunit
  | _ -> raise (FatalInBuiltin "debug_int")

let builtin_debug_bool = function
  | [Vbool i] -> print_endline (string_of_bool i); Vunit
  | _ -> raise (FatalInBuiltin "debug_bool")

let builtin_debug_float = function
  | [Vfloat i] -> print_endline (string_of_float i); Vunit
  | _ -> raise (FatalInBuiltin "debug_float")

(*
let builtin_pvt_funs_list =
  [
    (* int *)
    "pvt_int_add";
    "pvt_int_sub";
    "pvt_int_mul";
    "pvt_int_div";
    "pvt_int_mod";
    "pvt_int_lor";
    "pvt_int_lsl";
    "pvt_int_lsr";
    "pvt_int_land";
    "pvt_int_lxor";
    "pvt_int_ge";
    "pvt_int_gt";
    "pvt_int_le";
    "pvt_int_lt";
    "pvt_int_eq";
    "pvt_int_ne";
    "pvt_int_lnot";
    "pvt_int_neg";

    (* float *)
    "pvt_float_add";
    "pvt_float_sub";
    "pvt_float_mul";
    "pvt_float_div";
    "pvt_float_ge";
    "pvt_float_gt";
    "pvt_float_le";
    "pvt_float_lt";
    "pvt_float_eq";
    "pvt_float_ne";
    "pvt_float_neg";

    (* bool *)
    "pvt_bool_and";
    "pvt_bool_or";
    "pvt_bool_eq";
    "pvt_bool_ne";
    "pvt_bool_not";

    (* math functions *)
    "pvt_ceil";
    "pvt_floor";
    "pvt_round";
    "pvt_cos";
    "pvt_sin";
    "pvt_tan";
    "pvt_log";

    (* type cast *)
    "pvt_float_of_int";
    "pvt_int_of_pub";
    "pvt_float_of_pub";
    "pvt_bool_of_pub";
  ]

let builtin_pub_funs_list =
  [
    (* int *)
    "pub_int_add", builtin_int_add;
    "pub_int_sub", builtin_int_sub;
    "pub_int_mul", builtin_int_mul;
    "pub_int_div", builtin_int_div;
    "pub_int_mod", builtin_int_mod;
    "pub_int_lor", builtin_int_lor;
    "pub_int_lsl", builtin_int_lsl;
    "pub_int_lsr", builtin_int_lsr;
    "pub_int_land", builtin_int_land;
    "pub_int_lxor", builtin_int_lxor;
    "pub_int_ge", builtin_int_ge;
    "pub_int_gt", builtin_int_gt;
    "pub_int_le", builtin_int_le;
    "pub_int_lt", builtin_int_lt;
    "pub_int_eq", builtin_int_eq;
    "pub_int_ne", builtin_int_ne;
    "pub_int_lnot", builtin_int_lnot;
    "pub_int_neg", builtin_int_neg;

    (* float *)
    "pub_float_add", builtin_float_add;
    "pub_float_sub", builtin_float_sub;
    "pub_float_mul", builtin_float_mul;
    "pub_float_div", builtin_float_div;
    "pub_float_ge", builtin_float_ge;
    "pub_float_gt", builtin_float_gt;
    "pub_float_le", builtin_float_le;
    "pub_float_lt", builtin_float_lt;
    "pub_float_eq", builtin_float_eq;
    "pub_float_ne", builtin_float_ne;
    "pub_float_neg", builtin_float_neg;

    (* bool *)
    "pub_bool_and", builtin_bool_and;
    "pub_bool_or", builtin_bool_or;
    "pub_bool_eq", builtin_bool_eq;
    "pub_bool_ne", builtin_bool_ne;
    "pub_bool_not", builtin_bool_not;

    (* math functions *)
    "pub_ceil", builtin_ceil;
    "pub_floor", builtin_floor;
    "pub_round", builtin_round;
    "pub_cos", builtin_cos;
    "pub_sin", builtin_sin;
    "pub_tan", builtin_tan;
    "pi", builtin_pi;
    "pub_log", builtin_log;

    (* type cast *)
    "pub_float_of_int", builtin_float_of_int;
  ]

let builtin_pub_funs_tbl =
  Hashtbl.of_seq (List.to_seq builtin_pub_funs_list)

let builtin_funs_tbl =
  let nonpub_funs = List.map builtin_nonpub_wrapper builtin_pvt_funs_list in
  let pub_funs = List.map (fun (name, impl) -> name, builtin_public_wrapper impl) builtin_pub_funs_list in
  Hashtbl.of_seq (List.to_seq (nonpub_funs @ pub_funs))

exception UndefinedBuiltin of string

let builtin_pub_fun f_name =
  try
    Hashtbl.find builtin_pub_funs_tbl f_name
  with Not_found -> raise (UndefinedBuiltin f_name)

let builtin_fun f_name =
  try
    Hashtbl.find builtin_funs_tbl f_name
  with Not_found -> raise (UndefinedBuiltin f_name)
*)

(** This table contains evaluatable functions during ssim *)
let k0_funs =
  List.to_seq
  [
    (* int *)
    "k0pub_int_add", builtin_int_add;
    "k0pub_int_sub", builtin_int_sub;
    "k0pub_int_mul", builtin_int_mul;
    "k0pub_int_div", builtin_int_div;
    "k0pub_int_mod", builtin_int_mod;
    "k0pub_int_lor", builtin_int_lor;
    "k0pub_int_lsl", builtin_int_lsl;
    "k0pub_int_lsr", builtin_int_lsr;
    "k0pub_int_land", builtin_int_land;
    "k0pub_int_lxor", builtin_int_lxor;
    "k0pub_int_ge", builtin_int_ge;
    "k0pub_int_gt", builtin_int_gt;
    "k0pub_int_le", builtin_int_le;
    "k0pub_int_lt", builtin_int_lt;
    "k0pub_int_eq", builtin_int_eq;
    "k0pub_int_ne", builtin_int_ne;
    "k0pub_int_lnot", builtin_int_lnot;
    "k0pub_int_neg", builtin_int_neg;

    (* float *)
    "k0pub_float_add", builtin_float_add;
    "k0pub_float_sub", builtin_float_sub;
    "k0pub_float_mul", builtin_float_mul;
    "k0pub_float_div", builtin_float_div;
    "k0pub_float_ge", builtin_float_ge;
    "k0pub_float_gt", builtin_float_gt;
    "k0pub_float_le", builtin_float_le;
    "k0pub_float_lt", builtin_float_lt;
    "k0pub_float_eq", builtin_float_eq;
    "k0pub_float_ne", builtin_float_ne;
    "k0pub_float_neg", builtin_float_neg;

    (* bool *)
    "k0pub_bool_and", builtin_bool_and;
    "k0pub_bool_or", builtin_bool_or;
    "k0pub_bool_eq", builtin_bool_eq;
    "k0pub_bool_ne", builtin_bool_ne;
    "k0pub_bool_not", builtin_bool_not;

    (* math functions *)
    "k0pub_ceil", builtin_ceil;
    "k0pub_floor", builtin_floor;
    "k0pub_round", builtin_round;
    "k0pub_cos", builtin_cos;
    "k0pub_sin", builtin_sin;
    "k0pub_tan", builtin_tan;
    "pi", builtin_pi;
    "k0pub_log", builtin_log;
    "k0pub_exp", builtin_exp;

    (* type cast *)
    "k0pub_float_of_int", builtin_float_of_int;

    (* debug *)
    "k0pub_int_debug0", builtin_debug_int;
    "k0pub_bool_debug0", builtin_debug_bool;
    "k0pub_float_debug0", builtin_debug_float;
  ]
let k0_tbl =
  Hashtbl.of_seq k0_funs

let ssim_builtin f_name se_args =
  try
    let impl = Hashtbl.find k0_tbl f_name in
    builtin_wrapper impl se_args
  with Not_found -> SEbuiltin (f_name, se_args)

(** This table contains evaluatable functions during dsim by not ssim *)
let k1_funs =
  List.to_seq [
    (* int *)
    "k1pub_int_add", builtin_int_add;
    "k1pub_int_sub", builtin_int_sub;
    "k1pub_int_mul", builtin_int_mul;
    "k1pub_int_div", builtin_int_div;
    "k1pub_int_mod", builtin_int_mod;
    "k1pub_int_lor", builtin_int_lor;
    "k1pub_int_lsl", builtin_int_lsl;
    "k1pub_int_lsr", builtin_int_lsr;
    "k1pub_int_land", builtin_int_land;
    "k1pub_int_lxor", builtin_int_lxor;
    "k1pub_int_ge", builtin_int_ge;
    "k1pub_int_gt", builtin_int_gt;
    "k1pub_int_le", builtin_int_le;
    "k1pub_int_lt", builtin_int_lt;
    "k1pub_int_eq", builtin_int_eq;
    "k1pub_int_ne", builtin_int_ne;
    "k1pub_int_lnot", builtin_int_lnot;
    "k1pub_int_neg", builtin_int_neg;

    "k1pvt_int_add", builtin_int_add;
    "k1pvt_int_sub", builtin_int_sub;
    "k1pvt_int_mul", builtin_int_mul;
    "k1pvt_int_div", builtin_int_div;
    "k1pvt_int_mod", builtin_int_mod;
    "k1pvt_int_lor", builtin_int_lor;
    "k1pvt_int_lsl", builtin_int_lsl;
    "k1pvt_int_lsr", builtin_int_lsr;
    "k1pvt_int_land", builtin_int_land;
    "k1pvt_int_lxor", builtin_int_lxor;
    "k1pvt_int_ge", builtin_int_ge;
    "k1pvt_int_gt", builtin_int_gt;
    "k1pvt_int_le", builtin_int_le;
    "k1pvt_int_lt", builtin_int_lt;
    "k1pvt_int_eq", builtin_int_eq;
    "k1pvt_int_ne", builtin_int_ne;
    "k1pvt_int_lnot", builtin_int_lnot;
    "k1pvt_int_neg", builtin_int_neg;

    "k1plc_int_add", builtin_int_add;
    "k1plc_int_sub", builtin_int_sub;
    "k1plc_int_mul", builtin_int_mul;
    "k1plc_int_div", builtin_int_div;
    "k1plc_int_mod", builtin_int_mod;
    "k1plc_int_lor", builtin_int_lor;
    "k1plc_int_lsl", builtin_int_lsl;
    "k1plc_int_lsr", builtin_int_lsr;
    "k1plc_int_land", builtin_int_land;
    "k1plc_int_lxor", builtin_int_lxor;
    "k1plc_int_ge", builtin_int_ge;
    "k1plc_int_gt", builtin_int_gt;
    "k1plc_int_le", builtin_int_le;
    "k1plc_int_lt", builtin_int_lt;
    "k1plc_int_eq", builtin_int_eq;
    "k1plc_int_ne", builtin_int_ne;
    "k1plc_int_lnot", builtin_int_lnot;
    "k1plc_int_neg", builtin_int_neg;

    (* float *)
    "k1pub_float_add", builtin_float_add;
    "k1pub_float_sub", builtin_float_sub;
    "k1pub_float_mul", builtin_float_mul;
    "k1pub_float_div", builtin_float_div;
    "k1pub_float_ge", builtin_float_ge;
    "k1pub_float_gt", builtin_float_gt;
    "k1pub_float_le", builtin_float_le;
    "k1pub_float_lt", builtin_float_lt;
    "k1pub_float_eq", builtin_float_eq;
    "k1pub_float_ne", builtin_float_ne;
    "k1pub_float_neg", builtin_float_neg;

    "k1pvt_float_add", builtin_float_add;
    "k1pvt_float_sub", builtin_float_sub;
    "k1pvt_float_mul", builtin_float_mul;
    "k1pvt_float_div", builtin_float_div;
    "k1pvt_float_ge", builtin_float_ge;
    "k1pvt_float_gt", builtin_float_gt;
    "k1pvt_float_le", builtin_float_le;
    "k1pvt_float_lt", builtin_float_lt;
    "k1pvt_float_eq", builtin_float_eq;
    "k1pvt_float_ne", builtin_float_ne;
    "k1pvt_float_neg", builtin_float_neg;

    "k1plc_float_add", builtin_float_add;
    "k1plc_float_sub", builtin_float_sub;
    "k1plc_float_mul", builtin_float_mul;
    "k1plc_float_div", builtin_float_div;
    "k1plc_float_ge", builtin_float_ge;
    "k1plc_float_gt", builtin_float_gt;
    "k1plc_float_le", builtin_float_le;
    "k1plc_float_lt", builtin_float_lt;
    "k1plc_float_eq", builtin_float_eq;
    "k1plc_float_ne", builtin_float_ne;
    "k1plc_float_neg", builtin_float_neg;

    (* bool *)
    "k1pub_bool_and", builtin_bool_and;
    "k1pub_bool_or", builtin_bool_or;
    "k1pub_bool_eq", builtin_bool_eq;
    "k1pub_bool_ne", builtin_bool_ne;
    "k1pub_bool_not", builtin_bool_not;

    "k1pvt_bool_and", builtin_bool_and;
    "k1pvt_bool_or", builtin_bool_or;
    "k1pvt_bool_eq", builtin_bool_eq;
    "k1pvt_bool_ne", builtin_bool_ne;
    "k1pvt_bool_not", builtin_bool_not;

    "k1plc_bool_and", builtin_bool_and;
    "k1plc_bool_or", builtin_bool_or;
    "k1plc_bool_eq", builtin_bool_eq;
    "k1plc_bool_ne", builtin_bool_ne;
    "k1plc_bool_not", builtin_bool_not;

    (* math functions *)
    "k1pub_ceil", builtin_ceil;
    "k1pub_floor", builtin_floor;
    "k1pub_round", builtin_round;
    "k1pub_cos", builtin_cos;
    "k1pub_sin", builtin_sin;
    "k1pub_tan", builtin_tan;
    "k1pub_log", builtin_log;
    "k1pub_exp", builtin_exp;

    "k1pvt_ceil", builtin_ceil;
    "k1pvt_floor", builtin_floor;
    "k1pvt_round", builtin_round;
    "k1pvt_cos", builtin_cos;
    "k1pvt_sin", builtin_sin;
    "k1pvt_tan", builtin_tan;
    "k1pvt_log", builtin_log;
    "k1pvt_exp", builtin_exp;

    "k1plc_ceil", builtin_ceil;
    "k1plc_floor", builtin_floor;
    "k1plc_round", builtin_round;
    "k1plc_cos", builtin_cos;
    "k1plc_sin", builtin_sin;
    "k1plc_tan", builtin_tan;
    "k1plc_log", builtin_log;
    "k1plc_exp", builtin_exp;

    (* type cast *)
    "k1pub_float_of_int", builtin_float_of_int;
    "k1plc_float_of_int", builtin_float_of_int;

    "k1pub_int_of_k0", builtin_id;
    "k1pub_float_of_k0", builtin_id;
    "k1pub_bool_of_k0", builtin_id;

    "k1pub_int_of_pvt", builtin_id;
    "k1pub_float_of_pvt", builtin_id;
    "k1pub_bool_of_pvt", builtin_id;

    "k1pvt_int_of_pub", builtin_id;
    "k1pvt_float_of_pub", builtin_id;
    "k1pvt_bool_of_pub", builtin_id;
    
    "k1plc_int_of_pvt", builtin_id;
    "k1plc_float_of_pvt", builtin_id;
    "k1plc_bool_of_pvt", builtin_id;

    "k1pvt_int_of_plc", builtin_id;
    "k1pvt_float_of_plc", builtin_id;
    "k1pvt_bool_of_plc", builtin_id;
    
    "k1plc_int_of_pub", builtin_id;
    "k1plc_float_of_pub", builtin_id;
    "k1plc_bool_of_pub", builtin_id;

    (* debug *)
    "k0pub_int_debug1", builtin_debug_int;
    "k1pub_int_debug1", builtin_debug_int;

    "k0pub_bool_debug1", builtin_debug_bool;
    "k1pub_bool_debug1", builtin_debug_bool;

    "k0pub_float_debug1", builtin_debug_float;
    "k1pub_float_debug1", builtin_debug_float;
  ]

let k0k1_tbl =
  Hashtbl.of_seq (Seq.append k0_funs k1_funs)

let dsim_builtin f_name se_args =
  try
    let impl = Hashtbl.find k0k1_tbl f_name in
    builtin_wrapper impl se_args
  with Not_found -> SEbuiltin (f_name, se_args)
