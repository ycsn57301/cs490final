open Ast

type atomnode =
{
  atomnode_deps : (int ref) LValueMap.t; (* the node's dependent lvalue and its source node *)
}

type compnode =
{
  compnode_deps : int LValueMap.t; (* A set of dependent lvalues and their source node *)
  compnode_data_rev : int list;
}

(** ***** Union-find ***************************************** *)
type ufentry =
{
  ufentry_index : int;
  mutable ufentry_parent : int;
  mutable ufentry_rank : int;
}

let _debug_ufentry entry =
  Logs.debug (fun m -> m "%d -> %d" entry.ufentry_index entry.ufentry_parent)

(** Union-find with path-halving. *)
let uf_find entries index =
  let x = ref entries.(index) in
  while !x.ufentry_parent <> !x.ufentry_index do
    let parent = entries.(!x.ufentry_parent) in
    !x.ufentry_parent <- parent.ufentry_parent;
    x := parent
  done;
  !x.ufentry_index

(** Union-find union by rank. *)
let uf_union entries index1 index2 =
  let x = ref entries.(uf_find entries index1) in
  let y = ref entries.(uf_find entries index2) in
  if !x.ufentry_index <> !y.ufentry_index then begin
    let insert x y =
      !y.ufentry_parent <- !x.ufentry_index;
      if !x.ufentry_rank = !y.ufentry_rank then
        !x.ufentry_rank <- !x.ufentry_rank + 1
    in
    if !x.ufentry_rank < !y.ufentry_rank then
      insert y x
    else
      insert x y
  end

let uf_sameset entries index1 index2 =
  let index1' = uf_find entries index1 in
  let index2' = uf_find entries index2 in
  index1' = index2'

let merge_nodes (need_merge: lvalue_node -> bool) atomnodes =
  let size = List.length atomnodes in
  (* init union-find entries *)
  let ufentries = Array.init size (fun index ->
    {
      ufentry_index = index;
      ufentry_parent = index;
      ufentry_rank = 0;
    })
  in
  (* union entries based on dependencies *)
  List.iteri (fun index node ->
    LValueMap.iter (fun dep dep_index ->
      if need_merge dep then
        uf_union ufentries index !dep_index
    ) node.atomnode_deps;
  ) atomnodes;
  (* generate new graph of composite nodes.
     Convert inter dependencies between nodes and eliminate inner dependencies within each node.
  *)
  (* map from compindex to compnode *)
  let compgraph = Hashtbl.create 100 in
  (* map from atomindex to compindex, i -> j means atomnode i is part of compnode j *)
  let compindextbl = Hashtbl.create size in
  let create_compnode () =
    let cindex = Hashtbl.length compgraph in
    let cnode = {
      compnode_deps = LValueMap.empty;
      compnode_data_rev = []
    } in
    Hashtbl.add compgraph cindex cnode;
    cindex
  in
  List.iteri (fun aindex anode ->
    let parent_aindex = uf_find ufentries aindex in
    (* find or create a compnode *)
    let cindex =
      try
        Hashtbl.find compindextbl parent_aindex
      with Not_found ->
        create_compnode ()
    in
    Hashtbl.add compindextbl aindex cindex;
    let cnode = Hashtbl.find compgraph cindex in
    (* add anode into cnode *)
    let new_deps = LValueMap.fold (fun dep dep_aindex cdeps ->
      if need_merge dep then (* ignore merged dependency *)
        cdeps
      else if uf_sameset ufentries parent_aindex !dep_aindex then (* ignore inner dependency *)
        cdeps
      else (* add inter dependency *) begin
        let dep_cindex = Hashtbl.find compindextbl !dep_aindex in
        LValueMap.add dep dep_cindex cdeps
      end
    ) anode.atomnode_deps cnode.compnode_deps in
    let new_cnode = {
      compnode_deps = new_deps;
      compnode_data_rev = aindex :: cnode.compnode_data_rev;
    } in
    Hashtbl.replace compgraph cindex new_cnode
  ) atomnodes;
  Array.of_seq @@ Hashtbl.to_seq compgraph
