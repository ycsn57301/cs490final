(******************************************************************************)
(** This module is a subset of OCaml's Location module.
    We write our own module because the OCaml's Location module is unstable and
    part of compiler-libs. *)
(******************************************************************************)

open Lexing

type t = { loc_start : position; loc_end: position; loc_ghost : bool }

let in_file name =
  let pos = { Lexing.dummy_pos with pos_fname = name } in
  { loc_start = pos;
    loc_end = pos;
    loc_ghost = true;
  }

let none = in_file "_none_"
let is_none l = (l = none)

let curr lexbuf = {
    loc_start = lexbuf.lex_start_p;
    loc_end = lexbuf.lex_curr_p;
    loc_ghost = false
}

let init lexbuf fname =
  lexbuf.lex_curr_p <- {
    pos_fname = fname;
    pos_lnum = 1;
    pos_bol = 0;
    pos_cnum = 0;
  }

let symbol_rloc () = {
  loc_start = Parsing.symbol_start_pos ();
  loc_end = Parsing.symbol_end_pos ();
  loc_ghost = false;
}

let symbol_gloc () = {
  loc_start = Parsing.symbol_start_pos ();
  loc_end = Parsing.symbol_end_pos ();
  loc_ghost = true;
}

let rhs_loc n = {
  loc_start = Parsing.rhs_start_pos n;
  loc_end = Parsing.rhs_end_pos n;
  loc_ghost = false;
}

let rhs_interval m n = {
  loc_start = Parsing.rhs_start_pos m;
  loc_end = Parsing.rhs_end_pos n;
  loc_ghost = false;
}