type gen_lang =
  | EMP
  | SIEVE
  | ZOKRATES

type ou_cut_options = {
  ou_cut_proto_filename : string;
  ou_cut_noc : int;
  ou_cut_gen : gen_lang;
}

type ou_eval_options = {
  ou_eval_input_filename : string;
  ou_eval_prover_dirname : string;
  ou_eval_verifier_dirname : string;
  ou_eval_gen : gen_lang;
}

type ou_options =
  | OUcut of ou_cut_options
  | OUeval of ou_eval_options

(* TODO: allow user to specify output directory *)
let parse_options _ =
  let usage_msg = "ou cut --proto <file> --noc <noc> --gen <emp|sieve|zokrates>\nou eval --input <file> --proverdir <dir> --gen <emp|sieve|zokrates>" in
  (* mode selection *)
  let is_cut = ref true in
  let select_mode modename =
    if modename = "cut" then
      is_cut := true
    else if modename = "eval" then
      is_cut := false
    else begin
      print_endline modename;
      raise (Arg.Bad "Mode must be cut|eval")
    end
  in
  (* source file *)
  let opt_proto_filename = ref None in
  let set_proto filename = opt_proto_filename := Some filename in
  (* number of cuts *)
  let noc = ref 1 in
  (* input file *)
  let opt_input_filename = ref None in
  let set_input filename = opt_input_filename := Some filename in
  (* prover dir *)
  let opt_prover_dirname = ref None in
  let set_proverdir dirname = opt_prover_dirname := Some dirname in
  (* verifier dir *)
  let opt_verifier_dirname = ref None in
  let set_verifierdir dirname = opt_verifier_dirname := Some dirname in
  (* gen language *)
  let gen = ref EMP in
  let set_gen lang =
    match lang with
    | "emp" | "EMP" -> gen := EMP
    | "sieve" | "SIEVE" -> gen := SIEVE
    | "zokrates" | "ZOKRATES" | "ZoKrates" -> gen := ZOKRATES
    | _ -> raise (Arg.Bad "Generating language must be emp or sieve or zokrates")
  in
  (* start parsing *)
  let speclist =
    [("--noc", Arg.Set_int noc, "Number of cuts");
     ("--proto", Arg.String set_proto, "Protocol .ou file");
     ("--input", Arg.String set_input, "Input .ou file");
     ("--proverdir", Arg.String set_proverdir, "Prover's files directory");
     ("--verifierdir", Arg.String set_verifierdir, "Verifier's files directory");
     ("--gen", Arg.String set_gen, "Generating language: emp or sieve")] in
  Arg.parse speclist select_mode usage_msg;
  (* collect result *)
  if !is_cut then
    let proto_filename = match !opt_proto_filename with
      | Some filename -> filename
      | None -> raise (Arg.Bad "Missing protocol filename")
    in
    OUcut {
      ou_cut_proto_filename = proto_filename;
      ou_cut_noc = !noc;
      ou_cut_gen = !gen;
    }
  else
    let input_filename = match !opt_input_filename with
      | Some filename -> filename
      | None -> raise (Arg.Bad "Missing input filename")
    in
    let prover_dirname = match !opt_prover_dirname with
      | Some dirname -> dirname
      | None -> raise (Arg.Bad "Missing prover dirname")
    in
    let verifier_dirname = match !opt_verifier_dirname with
      | Some dirname -> dirname
      | None -> raise (Arg.Bad "Missing verifier dirname")
    in
    OUeval {
      ou_eval_input_filename = input_filename;
      ou_eval_prover_dirname = prover_dirname;
      ou_eval_verifier_dirname = verifier_dirname;
      ou_eval_gen = !gen;
    }