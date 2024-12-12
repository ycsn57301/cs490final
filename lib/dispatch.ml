
open Ast
open Parser
open Options
open Typecheck
open Ssim
open Analysis
open Util
(* open Rewrite *)
open Slicer
open Empgen
open Zokratesgen
open Dsim

type comm_data = {
  comm_program : scmd_node array;
  comm_blocks : int list array;
  comm_depnodes : depnode array;
  comm_fun_defs : fundef_node list;
  comm_typing_env : typing_env
}

exception OuFatal of string

let logs_info_endline (text: string) =
  Logs.info @@ fun m -> m "%s" text

let logs_debug_endline (text: string) =
  Logs.debug @@ fun m -> m "%s" text
(*
let _debug_blocks blocks =
  List.iter (fun block ->
    let scmd_text = String.concat "\n" (List.map string_of_scmd_node block.block_scmds) in
    let cost_text = string_of_int block.block_cut_cost ^ " " ^ string_of_int block.block_comput_cost in
    let pvt_in_text = String.concat ", " (List.map string_of_lvalue_node block.block_pvt_in) in
    Logs.debug (fun m -> m "%s\n\t\t\t\t\t\t\t\tcost:%-30s\n\t\t\t\t\t\t\t\tin: %-30s"
      scmd_text cost_text pvt_in_text)) blocks

let _debug_scmds blocks =
  List.iter (fun block ->
    let scmd_text = String.concat "\n" (List.map string_of_scmd_node block.block_scmds) in
    (* logs_debug_endline @@ "in\t\t" ^ String.concat ", " (List.map string_of_lvalue_node block.block_pvt_in);
    logs_debug_endline @@ "out\t\t" ^ String.concat ", " (List.map string_of_lvalue_node block.block_pvt_out); *)
    Logs.debug (fun m -> m "%s" scmd_text)) blocks
*)

let get_timestamp () = Unix.gettimeofday ()

let log_timefrom start_time msg =
  Logs.info (fun m ->
    let finish_time = Unix.gettimeofday () in
    m "%s: %f seconds" msg (finish_time -. start_time))

let create_dir_if_not_exist path =
  if Sys.file_exists path then
    begin if not (Sys.is_directory path) then
      raise (Sys_error (path ^ "exists but is not a directory"))
    end
  else Sys.mkdir path 0o755

let create_empty_file filename =
  let oc = open_out filename in
  close_out oc

let parse_protocol filename =
  let ch = open_in filename in
  let buf = Lexing.from_channel ch in
  let tops = try
      protocol_entry Lexer.token buf
    with Parsing.Parse_error
    | _ ->
      let curr = buf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let tok = Lexing.lexeme buf in
      Logs.err (fun m -> m "%s:%d:%d: Syntax error at token \"%s\"." filename line cnum tok);
      exit 1
  in
  close_in ch;
  tops

(** Parse protocol, run shallow-sim then cut it into pieces. *)
let run_cut protoname noc lang =
  (* extract a basename by stripping away the path and suffix *)
  let basename =
    let name_parts = String.split_on_char '/' protoname in
    let without_path = List.nth name_parts (List.length name_parts - 1) in
    List.hd (String.split_on_char '.' without_path) in
  (* parse input file *)
  let tops = parse_protocol protoname in
  (* print source file *)
  List.iter (fun d -> logs_debug_endline (string_of_p_top d)) tops;
  logs_info_endline "=============================";
  (* type check *)
  logs_info_endline "typecheck started";
  let gvars, fds, fxs, ty_env = typing_prog tops in
  let su_env = ty_env.typing_su_env in
  assert_function_is_defined ty_env "main";
  (* print source file *)
  List.iter (fun vd -> logs_debug_endline (string_of_gvardef_node vd)) gvars;
  List.iter (fun fd -> logs_debug_endline (string_of_fundef_node fd)) fds;
  logs_info_endline "=============================";
  (* shallow simulate program *)
  logs_info_endline "shallow-sim started";
  let ssim_start_time = get_timestamp () in
  let sprog, atomcall_env = ssim_prog gvars fds ty_env.typing_funs su_env in
  log_timefrom ssim_start_time "ssim time cost";
  let size = Array.length sprog in
  Array.iter (fun (sc, _) -> logs_debug_endline (string_of_scmd_node sc)) sprog;
  logs_info_endline "=============================";
  (* live variables analysis *)
  logs_info_endline "analysis started";
  let cutnodes = better_analysis sprog su_env atomcall_env in
  logs_info_endline "analysis finished";
  (*
  let blocks = live_variable_analysis sprog su_env atomcall_env in
  (* output *)
  (* _debug_blocks blocks; *)
  *)
  logs_info_endline "====================";
  logs_info_endline "slice start";
  logs_info_endline "====================";
  let slice_start_time = get_timestamp () in
  (* slice. Each chunk is a list of sorted ids. *)
  let blocks, depnodes = if noc > 1 then solve_opb sprog cutnodes noc
    else
      (* no cut. The dependent graph has only one node *)
      let block = list_range 0 size in
      Array.make 1 block, Array.make size {
        depnode_deps = [];
        depnode_defs = [];
      }
  in
  log_timefrom slice_start_time "slice time cost";
  (* print blocks for debugging *)
  Array.iteri (fun block_id block ->
    logs_debug_endline "";
    Logs.debug (fun m -> m "fragment %d #######################" block_id);
    List.iter (fun cmd_id ->
      let (sc, _) = sprog.(cmd_id) in
      logs_debug_endline (string_of_scmd_node sc)
    ) block
  ) blocks;
  (* generate EMP for each chunk *)
  logs_info_endline "====================";
  logs_info_endline "empgen start";
  logs_info_endline "====================";
  (* EMP related files *)
  let gen_EMP () =
    (* folders *)
    let prover_path = basename ^ "_prover/" in
    let verifier_path = basename ^ "_verifier/" in
    create_dir_if_not_exist prover_path;
    create_dir_if_not_exist verifier_path;
    (* TODO: should have created data directory for each individual prover and verifier *)
    create_dir_if_not_exist (prover_path ^ "data/");
    create_dir_if_not_exist (verifier_path ^ "data/");
    (* makefile *)
    output_makefile (prover_path   ^ "Makefile") noc;
    output_makefile (verifier_path ^ "Makefile") noc;
    (* header *)
    let headname = "common.h" in
    output_emp_head PROVER   (prover_path   ^ headname) su_env fds fxs gvars;
    output_emp_head VERIFIER (verifier_path ^ headname) su_env fds fxs gvars;
    (* common definitions *)
    output_emp_defs PROVER   (prover_path   ^ "common.cpp") su_env gvars fds;
    output_emp_defs VERIFIER (verifier_path ^ "common.cpp") su_env gvars fds;
    (* blocks *)
    Array.iteri (fun block_id block ->
      let part_name = "part" ^ string_of_int block_id ^ ".cpp" in
      let frag = Seq.map (fun cmd_id ->
        {
          cmdinfo_id = cmd_id;
          cmdinfo_cmd = fst sprog.(cmd_id);
          cmdinfo_deps = depnodes.(cmd_id).depnode_deps;
          cmdinfo_defs = depnodes.(cmd_id).depnode_defs;
        }
      ) (List.to_seq block) in
      output_emp PROVER   (prover_path   ^ part_name) su_env gvars frag noc;
      output_emp VERIFIER (verifier_path ^ part_name) su_env gvars frag noc) blocks;
    (* dependency *)
    create_empty_file (prover_path   ^ "depend.cpp");
    create_empty_file (verifier_path ^ "depend.cpp");
    (* serialize chunks *)
    logs_info_endline "====================";
    logs_info_endline "marshal start";
    logs_info_endline "====================";
    let ch = open_out_bin (prover_path ^ "ou-marshal") in
    let data = {
      comm_program = Array.map fst sprog;
      comm_depnodes = depnodes;
      comm_blocks = blocks;
      comm_fun_defs = fds;
      comm_typing_env = ty_env;
    } in
    Marshal.to_channel ch data [];
    close_out ch
  in
  (* ZoKrates related files *)
  let gen_ZoKrates () =
    let genpath = basename ^ "/" in
    create_dir_if_not_exist genpath;
    Array.iteri (fun block_id block ->
      let part_name = "part" ^ string_of_int block_id ^ ".zok" in
      let frag = Seq.map (fun cmd_id ->
        {
          cmdinfo_id = cmd_id;
          cmdinfo_cmd = fst sprog.(cmd_id);
          cmdinfo_deps = depnodes.(cmd_id).depnode_deps;
          cmdinfo_defs = depnodes.(cmd_id).depnode_defs;
        }
      ) (List.to_seq block) in
      output_zokrates (genpath ^ part_name) su_env gvars frag noc) blocks
  in
  begin match lang with
  | EMP -> gen_EMP ()
  | ZOKRATES -> gen_ZoKrates ()
  | _ -> raise (OuFatal "Language is not supported yet")
  end

let run_eval inputname prover_path verifier_path =
  logs_info_endline "====================";
  logs_info_endline "unmarshal start";
  logs_info_endline "====================";
  let prover_path = prover_path ^ "/" in
  let verifier_path = verifier_path ^ "/" in
  let marshal_ch = open_in_bin (prover_path ^ "ou-marshal") in
  let data = Marshal.from_channel marshal_ch in
  let sprog = data.comm_program in
  let depnodes = data.comm_depnodes in
  let blocks = data.comm_blocks in
  let fds = data.comm_fun_defs in
  let ty_env = data.comm_typing_env in
  let noc = Array.length blocks in
  (* let (chunks, fds, gvars, ty_env) = Marshal.from_channel marshal_ch in *)
  close_in marshal_ch;
  (*
  (* print unmarshaled program for debugging *)
  List.iter (fun chunk ->
    logs_debug_endline "";
    logs_debug_endline "pvt-in ##################################";
    logs_debug_endline (String.concat ", " (List.map string_of_lvalue_node chunk.chunk_pvt_in));
    logs_debug_endline "protocol fragment ########################";
    List.iter (fun sc ->
      logs_debug_endline (string_of_scmd_node sc)) chunk.chunk_prog) chunks;
  *)
  (* parse input file *)
  logs_info_endline "====================";
  logs_info_endline "parse start";
  logs_info_endline "====================";
  let tops = parse_protocol inputname in
  (* typecheck input file *)
  logs_info_endline "====================";
  logs_info_endline "typecheck start";
  logs_info_endline "====================";
  let (*input_gvars*)_, input_fds, _, input_ty_env = typing_prog ~env:ty_env tops in
  let input_su_env = input_ty_env.typing_su_env in
  (* assert_function_is_defined input_ty_env "init"; *)
  (* start deep-sim chunks *)
  logs_info_endline "====================";
  logs_info_endline "deep-sim start";
  logs_info_endline "====================";
  let dsim_start_time = get_timestamp () in
  let deps = dsim_prog (input_fds @ fds) input_su_env sprog depnodes in
  (* output dependent lvalues *)
  Array.iteri (fun block_id block ->
    let sync_name = "sync" ^ string_of_int block_id ^ ".cpp" in
    let frag = Seq.map (fun cmd_id ->
      {
        cmdinfo_id = cmd_id;
        cmdinfo_cmd = sprog.(cmd_id);
        cmdinfo_deps = depnodes.(cmd_id).depnode_deps;
        cmdinfo_defs = depnodes.(cmd_id).depnode_defs;
      }
    ) (List.to_seq block) in
    let asgns = Seq.map (fun cmd_id ->
      deps.(cmd_id)
    ) (List.to_seq block) in
    (* output_emp_sync *)
    (* TODO: The sync for verifier should be run without asgns, also extract the produce_n out as separate functions *)
    output_emp_sync PROVER   (prover_path   ^ sync_name) asgns frag noc;
    output_emp_sync VERIFIER (verifier_path ^ sync_name) asgns frag noc
  ) blocks;
  (* output dependent functions *)
  output_emp_depend PROVER (prover_path ^ "depend.cpp") input_su_env input_fds;
  log_timefrom dsim_start_time "dsim time cost"

let dispatch () =
  Logs.set_reporter (Logs_fmt.reporter ());
  (* log levels: App, Error, Warning, Info, Debug *)
  Logs.set_level (Some Logs.Info);
  let mode = Options.parse_options () in
  match mode with
  | OUcut options ->
    run_cut options.ou_cut_proto_filename options.ou_cut_noc options.ou_cut_gen
  | OUeval options ->
    run_eval options.ou_eval_input_filename options.ou_eval_prover_dirname options.ou_eval_verifier_dirname
