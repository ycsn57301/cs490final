(* open Ast *)
open Analysis

let solve_opb sprog cutnodes noc =
  let input_name = "/tmp/OPBInput.txt" in
  let result_name = "/tmp/OPBResult.txt" in
  let cmd = "python3 ILPBuilder/OPB.py > /tmp/OPBStat.txt" in
  (* output dependencies, costs and noc *)
  let output_config () =
    let oc = open_out input_name in
    output_string oc ("meta info\n");
    Printf.fprintf oc "%d, %d\n" (Array.length cutnodes) noc;
    output_string oc ("node info\n");
    Array.iteri (fun index (_, cost) ->
      Printf.fprintf oc "%d, %d\n" index cost
    ) sprog;
    output_string oc ("edge info\n");
    Array.iteri (fun index cutnode ->
      Hashtbl.iter (fun src_index opt_deps ->
        match opt_deps with
        | Uncuttable -> Printf.fprintf oc "%d, %d, 0, 0\n" src_index index
        | Cuttable deps ->
          let acc_cost = ref 0 in
          List.iter (fun (_, cut_cost) -> acc_cost := cut_cost + !acc_cost) deps;
          Printf.fprintf oc "%d, %d, %d, 1\n" src_index index !acc_cost
      ) cutnode.cutnode_deps
    ) cutnodes;
    close_out oc
  in
  (* collect result *)
  let parse_result () =
    let ic = open_in result_name in
    let segments = Array.init noc (fun _ -> []) in
    for i = 0 to noc - 1 do
      let line = input_line ic in
      if String.length line <> 0 then
        let segment = List.map int_of_string (String.split_on_char ' ' line) in
        segments.(i) <- segment
    done;
    close_in ic;
    segments
  in
  (*
  let collect_deps segment =
    let lvs = ref LValueTree.empty in
    List.iter (fun cmd_id ->
      let cutnode = cutnodes.(cmd_id) in
      let tbl = cutnode.cutnode_deps in
      Hashtbl.iter (fun src_index cut ->
        match cut with
        | Uncuttable -> ()
        | Cuttable lst ->
          if not @@ List.mem src_index segment then (* inter dependency *)
            List.iter (fun (lv, _) ->
              lvs := LValueTree.add lv !lvs
            ) lst
      ) tbl;
      ()
    ) segment;
    !lvs
  in
  *)
  (* ******* start ************* *)
  output_config ();
  (* run external solver *)
  let ret_status = Sys.command cmd in
  if ret_status <> 0 then raise (Failure "OPB solver failed");
  Logs.info (fun m -> m "solver finished");
  let segments = parse_result () in
  Logs.info (fun m -> m "finished parsing solver result");
  (* clean up temporary files *)
  (* Sys.remove input_name; *)
  (* Sys.remove result_name; *)
  (* lookup table from command id to segment id *)
  let segtbl = Hashtbl.create (Array.length cutnodes) in
  Array.iteri (fun seg_id segment ->
    List.iter (fun cmd_id ->
      (* Logs.debug (fun m -> m "segment %d has %d" seg_id cmd_id); *)
      Hashtbl.add segtbl cmd_id seg_id
    ) segment
  ) segments;
  Logs.debug (fun m -> m "Created segtbl");
  let same_segment id1 id2 =
    Hashtbl.find segtbl id1 = Hashtbl.find segtbl id2
  in
  (* collect inter dependencies for every node *)
  let depnodes = Array.init (Array.length cutnodes) (fun _ -> {
    depnode_deps = [];
    depnode_defs = [];
  }) in
  Array.iteri (fun dst_id cutnode ->
    Hashtbl.iter (fun src_id opt_deps ->
      match opt_deps with
      | Uncuttable -> ()
      | Cuttable deps ->
        (* dst_id's command depends on src_id's command with deps *)
        if not @@ same_segment dst_id src_id then begin
          let lvs = List.map fst deps in
          depnodes.(dst_id).depnode_deps <- (src_id, Hashtbl.find segtbl src_id, lvs) :: depnodes.(dst_id).depnode_deps;
          depnodes.(src_id).depnode_defs <- (dst_id, Hashtbl.find segtbl dst_id, lvs) :: depnodes.(src_id).depnode_defs
        end
    ) cutnode.cutnode_deps
  ) cutnodes;
  segments, depnodes

(*
  (* collect inter dependencies for every block *)
  let blocks_deps = Array.mapi (fun block_id block ->
    let deps = ref LValueTree.empty in
    List.iter (fun cmd_id ->
      let (sc, _) = sprog.(cmd_id) in
      ()
    ) block;
    !deps
  ) blocks in
  for i = 0 to noc - 1 do
    let deps = ref Array.
  done;
*)
(*
(** Slice blocks into chunks.
    Return a list of cutting points. A cutting point x means
    cut before x-th block (count from 0).
    The last cutting point is always the end of all blocks. *)
let solve_ilp blocks noc =
  let cmd = "python ILPBuilder/ILPbuilder.py > /dev/null" in
  (* output costs and noc *)
  let oc = open_out "/tmp/ILPinput.txt" in
  output_string oc (String.concat " " (List.map (fun block -> string_of_int block.block_comput_cost) blocks));
  output_char oc '\n';
  output_string oc (String.concat " " (List.map (fun block -> string_of_int block.block_cut_cost) blocks));
  output_char oc '\n';
  output_string oc (string_of_int noc ^ "\n");
  close_out oc;
  (* run external ILP solver *)
  let ret_status = Sys.command cmd in
  if ret_status <> 0 then raise (Failure "ILP solver failed");
  (* collect result *)
  let ic = open_in "/tmp/ILPresult.txt" in
  let raw_cut_points = input_line ic in
  close_in ic;
  Sys.remove "/tmp/ILPinput.txt";
  Sys.remove "/tmp/ILPresult.txt";
  (* assume the result is a list of integers split by exactly one space *)
  let cut_points = List.map int_of_string (String.split_on_char ' ' raw_cut_points) in
  cut_points
*)

(* let output_chunks file_prefix blocks cut_points common_defs =
  let total_cut_points = List.length cut_points in
  let idx = ref 0 in
  let need_init = ref true in
  let next_cut_point, remaining_cut_points = match cut_points with
    | point :: points -> ref point, ref points
    | _ -> raise (Failure "no cut point found")
  in
  let file_name () =
    let chunk_num = total_cut_points - 1 - (List.length !remaining_cut_points) in
    file_prefix ^ "_part" ^ (string_of_int chunk_num) ^ ".ou" in
  let oc = ref (open_out (file_name ())) in
  List.iter (fun block ->
    if !need_init then begin
      (* output function and struct definitions *)
      output_string !oc common_defs;
      (* output live-in *)
      Printf.fprintf !oc "\n#live-in: %s\n"
        (String.concat ", " (List.map (string_of_lvalue ~type_hint:true) block.block_live_in));
      need_init := false
    end;
    (* output command *)
    let scmd_text = string_of_scmd ~type_hint:true block.block_scmd in
    Printf.fprintf !oc "%s\n" scmd_text;
    idx := !idx + 1;
    (* check if reached the next cutting point *)
    if !idx = !next_cut_point then begin
      (* output live-out *)
      Printf.fprintf !oc "\n#live-out: %s\n"
        (String.concat ", " (List.map (string_of_lvalue ~type_hint:true) block.block_live_out));
      close_out !oc;
      match !remaining_cut_points with
      (* still have non-trivial cutting points *)
      | point :: points ->
        (* consume cut_point *)
        next_cut_point := point;
        remaining_cut_points := points;
        (* open next file *)
        oc := open_out (file_name ());
        need_init := true
      (* we have just consumed the second last cutting point *)
      | _ -> ()
    end
    ) blocks *)

(*
(** Generate some chunks based on cut points.
    This is for debug only. Should be deleted soon. *)
let gen_chunks blocks cut_points =
  let idx = ref 0 in
  let need_init = ref true in
  let next_cut_point, remaining_cut_points = match cut_points with
    | point :: points -> ref point, ref points
    | _ -> raise (Failure "no cut point found")
  in
  let chunks = ref [] in
  let current_prog = ref [] in
  let current_pvt_in = ref [] in
  List.iter (fun block ->
    if !need_init then begin
      (* output live-in *)
      current_pvt_in := block.block_pvt_in;
      need_init := false
    end;
    (* output command *)
    current_prog := !current_prog @ block.block_scmds;
    idx := !idx + 1;
    (* check if reached the next cutting point *)
    if !idx = !next_cut_point then begin
      (* output chunk *)
      let chunk = {
        chunk_pvt_in = !current_pvt_in;
        chunk_prog = !current_prog }
      in
      chunks := !chunks @ [chunk];
      (* prepare *)
      current_prog := [];
      match !remaining_cut_points with
      (* still have non-trivial cutting points *)
      | point :: points ->
        (* consume cut_point *)
        next_cut_point := point;
        remaining_cut_points := points;
        need_init := true
      (* we have just consumed the second last cutting point *)
      | _ -> ()
    end
    ) blocks;
  !chunks
*)