open Ast
open Sim
(* open Depgraph *)

exception FatalInAnalysis of string
exception LValueIsIlltyped of lvalue
exception HasK2Value
exception TODOAnalysis

(*
type liveblock =
{
  block_pvt_in : lvalue_node list;
  block_scmds : scmd_node list;
  block_cut_cost : int; (* linear to the size of live in *)
  block_comput_cost : int;
}
*)
let rec indivisible_base_of_slexpr sle =
  match lvalue_of_slexpr sle with
  | Some lv -> lv
  | None ->
    match sle.slexpr with
    | SEvar _ -> raise (FatalInAnalysis "indivisible_base_of_slexpr")
    | SEindex (arr, _, _) -> indivisible_base_of_slexpr arr
    | SEfield (st, _) -> indivisible_base_of_slexpr st

let rec refs_in_sexpr su_env ignore_pointer se =
  match se.sexpr with
  | SEunit
  | SEint _
  | SEfloat _
  | SEbool _
  | SEnull -> LValueTree.empty
  | SEref lv ->
    if ignore_pointer then LValueTree.empty
    else LValueTree.singleton lv
  | SElexpr le -> refs_in_slexpr su_env ignore_pointer le
  | SEarrayinit (_, se_inits) -> lvaluetree_unions (List.map (refs_in_sexpr su_env ignore_pointer) se_inits)
  | SEstructinit asgns -> lvaluetree_unions (List.map (fun (_, se) -> refs_in_sexpr su_env ignore_pointer se) asgns)
  | SEbuiltin (_, args) -> lvaluetree_unions (List.map (refs_in_sexpr su_env ignore_pointer) args)
and nonbase_refs_in_slexpr su_env ignore_pointer sle =
  match sle.slexpr with
  | SEvar _ -> LValueTree.empty
  | SEindex (arr, _, index) -> LValueTree.union (nonbase_refs_in_slexpr su_env ignore_pointer arr) (refs_in_sexpr su_env ignore_pointer index)
  | SEfield (st, _) -> nonbase_refs_in_slexpr su_env ignore_pointer st

(** Examples:
    x -> {x}
    a[4] -> {a[4]}
    s.f -> {s.f}
    a[idx+n] -> {a, idx, n}
    a[idx].f -> {a, idx}
    s.a[idx] -> {s.a, idx}
    a[i][j] -> {a, i, j}
    Note: it does not have to be so complicated if we only allow zkram to have primitive elements,
    but we have to be prepared for the future extension. *)
and refs_in_slexpr su_env ignore_pointer sle =
  let lv_base = indivisible_base_of_slexpr sle in
  (* let base = indivisible_K1K2_lvalues su_env lv_base in *)
  (* let base = LValueSet.singleton (indivisible_base_of_slexpr sle) in *)
  let nonbase = nonbase_refs_in_slexpr su_env ignore_pointer sle in
  LValueTree.add lv_base nonbase

let rec k1_cost_of_type su_env = function
  | Tunit | Tref _
  | Tbool (Public K0Public) | Tint (Public K0Public) | Tfloat (Public K0Public) -> 0
  | Tbool (Public K1Public) | Tint (Public K1Public) | Tfloat (Public K1Public) -> 0
  | Tbool (Private K1Private) -> 1
  | Tint (Private K1Private) -> 32
  | Tfloat (Private K1Private) -> 32
  | Tbool (Plocal K1Plocal) -> 0
  | Tint (Plocal K1Plocal) -> 0
  | Tfloat (Plocal K1Plocal) -> 0
  | Tbool (Public K2Public) | Tint (Public K2Public) | Tfloat (Public K2Public)
  | Tbool (Private K2Private) | Tint (Private K2Private) | Tfloat (Private K2Private)
  | Tbool (Plocal K2Plocal) | Tint (Plocal K2Plocal) | Tfloat (Plocal K2Plocal) -> raise HasK2Value
  | Tarray (elem_ty, _, size) -> size * (k1_cost_of_type su_env elem_ty)
  | Tstruct st_name ->
    let st = find_struct su_env st_name in
    List.fold_left (fun acc (field_ty, _) -> acc + k1_cost_of_type su_env field_ty) 0 st.struct_fields

let rec type_has_K2 su_env ty =
  match ty with
  | Tunit | Tref _ -> false
  | Tbool sec | Tint sec | Tfloat sec -> knwlvl_of_seclvl sec = K2
  | Tarray (elem_ty, _, _) -> type_has_K2 su_env elem_ty
  | Tstruct st_name ->
    let st = find_struct su_env st_name in
    List.exists (fun (field_ty, _) -> type_has_K2 su_env field_ty) st.struct_fields

type atomnode =
{
  atomnode_deps : (lvalue_node * int ref) list; (* the node's dependent lvalue and its source node *)
}

let _debug_atomnode node =
  List.iter (fun (lv, src_index) ->
    Logs.debug @@ fun m -> m "%d <- %s" !src_index (string_of_lvalue_node lv)) node.atomnode_deps

let live_component su_env atomcall_env sc =
  let defs = match sc.scmd with
  | SCdef (ty, alias, _) ->
    let lv = mk_lvalue (Vvar alias) ty in
    LValueTree.singleton lv
  | SCasgn (sle, _) ->
    begin match lvalue_of_slexpr sle with
    | Some lv -> LValueTree.singleton lv
    | None -> LValueTree.empty
    end
  | SCassert _ -> LValueTree.empty
  | SCcall (ty, alias, _, _, _) ->
    let info = atomcall_info atomcall_env alias in
    let lv = mk_lvalue (Vvar alias) ty in
    LValueTree.add lv info.liveinfo_K1K2_W
  | SCsandboxcall (ty, _, alias, _, _) ->
    let lv = mk_lvalue (Vvar alias) ty in
    LValueTree.singleton lv
  in
  let refs = match sc.scmd with
  | SCdef (_, _, se) -> refs_in_sexpr su_env true se
  | SCasgn (sle, se) -> LValueTree.union (nonbase_refs_in_slexpr su_env true sle) (refs_in_sexpr su_env true se)
  | SCassert se -> refs_in_sexpr su_env true se
  | SCcall (_, alias, _, args, _) ->
    let args_pvtR = List.fold_left (fun pvtR arg ->
      LValueTree.union pvtR (refs_in_sexpr su_env true arg)) LValueTree.empty args in
    let body_info = atomcall_info atomcall_env alias in
    let body_pvtR = body_info.liveinfo_K1K2_R in
    LValueTree.union args_pvtR body_pvtR
  | SCsandboxcall (_, _, _, _, args) ->
    lvaluetree_unions (List.map (refs_in_sexpr su_env false) args)
  in
  defs, refs

(** Convert a sequential program into a dependency graph. *)
let gen_depgraph (sprog : (scmd_node * int) array) su_env atomcall_env =
  let size = Array.length sprog in
  (* a mapping from lvalue to a block id that reads this lvalue. An lvalue may be depended by multiple blocks. *)
  let live_env : (int ref) LValueHashtbl.t = LValueHashtbl.create 100 in
  let atomnodes = Array.make size {
    atomnode_deps = []
  } in
  (* let live_out = ref LValueTree.empty in *)
  for index = size-1 downto 0 do
    let (sc, _) = sprog.(index) in
    let defs, refs = live_component su_env atomcall_env sc in
    (* resolve defs. Find all records that depend on lvalues in `defs`, then label them with `index`. *)
    LValueTree.iter su_env (fun lv_base ->
      let lvs = indivisible_K1K2_lvalues su_env lv_base in
      List.iter (fun lv ->
        while LValueHashtbl.mem live_env lv do
          let cell = LValueHashtbl.find live_env lv in
          cell := index;
          LValueHashtbl.remove live_env lv
        done
      ) lvs
    ) (LValueTree.union defs refs); (* NOTE: this should have been defs, but we allow refs to also resolve dependencies for better result *)
    (* live-in = live-out - (new-defs + atom-defs) + refs *)
    (* let live_in = LValueTree.union (LValueTree.diff su_env !live_out defs) refs in *)
    (* convert `live_in` into dependencies and record them in `live_env` *)
    let deps = ref [] in
    LValueTree.iter su_env (fun lv ->
      let cell = ref (-1) in
      (* add all atomic lvalues into `live_env` *)
      let lvs = indivisible_K1K2_lvalues su_env lv in
      List.iter (fun lv ->
        LValueHashtbl.add live_env lv cell
      ) lvs;
      deps := (lv, cell) :: !deps;
    ) refs;
    (* construct a dependency node *)
    let node = {
      atomnode_deps = !deps;
    } in
    atomnodes.(index) <- node
    (* live_out := live_in *)
  done;
  atomnodes

type 'a cutoption =
| Uncuttable
| Cuttable of 'a

type cutnode =
{
  cutnode_deps : (int, (lvalue_node * int) list cutoption) Hashtbl.t; (* the node's dependent lvalue and its cost *)
}

let _debug_cutnode node =
  Hashtbl.iter (fun src_index deps ->
    let deps_text = match deps with
    | Uncuttable -> "*"
    | Cuttable deps ->
      "[" ^ String.concat ", " (List.map (fun (lv, _) -> string_of_lvalue_node lv) deps) ^ "]"
    in
    Logs.debug @@ fun m -> m "%d <- %s" src_index deps_text
  ) node.cutnode_deps

  type depnode =
  {
    mutable depnode_deps : (int * int * lvalue_node list) list; (* src command id, src chunk id, lvalues *)
    mutable depnode_defs : (int * int * lvalue_node list) list; (* dst command id, dst chunk id, lvalues *)
  }
(*
  let _debug_depnode node =
    Hashtbl.iter (fun src_index deps ->
      let deps_text = "[" ^ String.concat ", " (List.map string_of_lvalue_node deps) ^ "]" in
      Logs.debug @@ fun m -> m "%d <- %s" src_index deps_text
    ) node.depnode_deps
*)
let better_analysis (sprog : (scmd_node * int) array) su_env atomcall_env =
  let size = Array.length sprog in
  let atomnodes = gen_depgraph sprog su_env atomcall_env in
  (* debug atom nodes *)
  Logs.debug (fun m -> m "=============================");
  Logs.debug (fun m -> m "atomnodes");
  Logs.debug (fun m -> m "=============================");
  Array.iteri (fun index node ->
    Logs.debug @@ fun m -> m "=== %d ===" index;
    Logs.debug @@ fun m -> m "%s" (string_of_scmd_node (fst sprog.(index)));
    _debug_atomnode node) atomnodes;
  (* merge dependencies that rely on the same node *)
  let cutnodes = Array.init size (fun index ->
    let anode = atomnodes.(index) in
    let tbl = Hashtbl.create 1 in
    List.iter (fun (lv, src_index) ->
      (* add the cutting cost of lv to a list of dependencies *)
      let add_dep deps =
        let ty = type_of_lvalue lv in
        try Cuttable ((lv, k1_cost_of_type su_env ty) :: deps)
        with HasK2Value -> Uncuttable
      in
      begin match Hashtbl.find_opt tbl !src_index with
      | None -> Hashtbl.add tbl !src_index (add_dep [])
      | Some Uncuttable -> ()
      | Some (Cuttable deps) -> Hashtbl.replace tbl !src_index (add_dep deps)
      end
    ) anode.atomnode_deps;
    { cutnode_deps = tbl }
  ) in
  (* debug *)
  Logs.debug (fun m -> m "=============================");
  Logs.debug (fun m -> m "cutnodes");
  Logs.debug (fun m -> m "=============================");
  Array.iteri (fun index node ->
    Logs.debug (fun m -> m "=== %d ===" index);
    Logs.debug @@ fun m -> m "%s" (string_of_scmd_node (fst sprog.(index)));
    _debug_cutnode node
  ) cutnodes;
  cutnodes

let list_of_lvaluetree su_env s =
  let res = ref [] in
  LValueTree.iter su_env (fun lv -> res := lv :: !res) s;
  !res
(*
(** reference: https://www.cl.cam.ac.uk/teaching/1819/OptComp/slides/lecture03.pdf
    Note: since there's no branch, we do not have to repeatly compute a fixpoint.
    So the time complexity is linear to the size of sprog. *)
let live_variable_analysis (sprog : (scmd_node * int) Array.t) su_env atomcall_env =
  let blocks = ref [] in
  let scs = ref [] in
  let live_out = ref LValueTree.empty in
  let acc_cost = ref 0 in
  let size = Array.length sprog in
  for i = size - 1 downto 0 do
    (* The loop scans the program from end to beginning.
      Each iteration takes in
       * `blocks`: all generated blocks,
       * `scs`: a list of commands that can not be divided,
       * `live_out`: the live-out of sc (or the live-in of the next command),
       * `acc_cost`: the computation cost of scs,
       * `sc`: a command that we are about to merge,
       * `cost`: the computation cost of `sc`. *)
    let (sc, cost) = sprog.(i) in
    let defs, refs = live_component su_env atomcall_env sc in
    (* live-in = live-out - (new-defs + atom-defs) + refs *)
    let live_in = LValueTree.union (LValueTree.diff su_env !live_out defs) refs in
    try
      let cut_cost = ref 0 in
      LValueTree.iter su_env (fun lv ->
        let ty = type_of_lvalue lv in
        cut_cost := k1_cost_of_type su_env ty + !cut_cost
      ) live_in;
      let block = {
        block_pvt_in = list_of_lvaluetree su_env live_in;
        block_scmds = sc :: !scs;
        block_cut_cost = !cut_cost;
        block_comput_cost = cost + !acc_cost;
      } in
      blocks := block :: !blocks;
      scs := [];
      live_out := live_in;
      acc_cost := 0
    with HasK2Value -> begin (* merge commands that share K2 values into a block *)
      scs := sc :: !scs;
      live_out := live_in;
      acc_cost := cost + !acc_cost
    end
  done;
  if !scs = [] then !blocks
  else
    let block = {
      block_pvt_in = [];
      block_scmds = !scs;
      block_cut_cost = 0;
      block_comput_cost = !acc_cost;
    } in
    block :: !blocks
*)