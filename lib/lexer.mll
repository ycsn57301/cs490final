{
open Parser

let keyword_table =
  let tbl = Hashtbl.create 40 in
  List.iter (fun (key, value) -> Hashtbl.add tbl key value) [
    (* types *)
    "int", TINT;
    "bool", TBOOL;
    "float", TFLOAT;
    "unit", TUNIT;
    "pvt", PRIVATE;
    "pub", PUBLIC;
    "plc", PLOCAL;
    (*
    "KNW0", KNW0;
    "KNW1", KNW1;
    "KNW2", KNW2;
    *)
    "pvt1", PRIVATE1;
    "pvt2", PRIVATE2;
    "pub0", PUBLIC0;
    "pub1", PUBLIC1;
    "pub2", PUBLIC2;
    "plc1", PLOCAL1;
    "plc2", PLOCAL2;
    "struct", STRUCT;
    "int8", TINT;
    "int16", TINT;
    "int32", TINT;
    "int64", TINT;
    "uint8", TINT;
    "uint16", TINT;
    "uint32", TINT;
    "uint64", TINT;
    (* constants *)
    "null", NULL;
    "true", TRUE;
    "false", FALSE;
    (* operators *)
    (* commands *)
    "if", IF;
    "else", ELSE;
    "while", WHILE;
    "for", FOR;
    "return", RETURN;
    "break", BREAK;
    "continue", CONTINUE;
    "assert", ASSERT;
    (* others *)
    "extern", DECLARE;
    "atomic", ATOMIC_ANNO;
    "plocal1", PLOCAL1_ANNO;
    "plocal2", PLOCAL2_ANNO;
    "blackbox1", BLACKBOX1_ANNO;
    "blackbox2", BLACKBOX2_ANNO;
  ];
  tbl
(*
type macro_value =
| Mint of int
| Mfloat of float
*)
let macro_table : (string, token) Hashtbl.t = Hashtbl.create 20

let macro_name = ref ""

let comment_level = ref 0

let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- { pos with
    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
    Lexing.pos_bol = pos.Lexing.pos_cnum;
  }
}

let newline = ('\010' | "\013\010")
let identstart = ['A'-'Z' 'a'-'z' '_']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']

let decimal_literal =
  ['1'-'9'] ['0'-'9']* | '0'
let decimal_float_literal =
  (['1'-'9'] ['0'-'9']* | '0') '.' ['0'-'9']+
let hex_literal =
  '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']*
let oct_literal_C =
  '0' ['0'-'7']+  (* NOTE: C syntax, different from OCaml *)
let oct_literal_OCaml =
  '0' ['o' 'O'] ['0'-'7']+
let bin_literal =
  '0' ['b' 'B'] ['0'-'1']+
let int_literal =
  decimal_literal | hex_literal | oct_literal_OCaml | bin_literal

rule token = parse
  | newline { incr_linenum lexbuf; token lexbuf }
  | [' ' '\009' '\012'] +  { token lexbuf }
  | eof { EOF }
  | "/*" { comment lexbuf; token lexbuf }

  | int_literal { INT (- int_of_string ("-" ^ Lexing.lexeme lexbuf)) }
  | oct_literal_C { INT (- int_of_string ("- 0o" ^ Lexing.lexeme lexbuf)) }
  | decimal_float_literal { FLOAT (Float.of_string (Lexing.lexeme lexbuf)) }

  | identstart identchar*
    { let s = Lexing.lexeme lexbuf in
      try
        Hashtbl.find keyword_table s
      with Not_found ->
      try
        Hashtbl.find macro_table s
      with Not_found -> IDENT s }
  | "#define" { macro lexbuf; token lexbuf }
  | "=" { ASSIGN }
  | "+" { ADD }
  | "-" { SUB }
  | "*" { MUL }
  | "/" { DIV }
  | "%" { MOD }
  | "==" { EQ }
  | "!=" { NE }
  | "<=" { LE }
  | "<" { LT }
  | ">=" { GE }
  | ">" { GT }
  | "!" { NOT }
  | "&&" { AND }
  | "||" { OR }
  | "~" { LNOT }
  | "&" { LAND }
  | "|" { LOR }
  | "^" { LXOR }
  | "<<" { LSL }
  | ">>" { LSR }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | ";" { SEMICOLON }
  | "," { COMMA }
  | "." { DOT }
  | "->" { RARROW }
  | "//" { let _ = line_comment lexbuf in token lexbuf }  

  and comment = parse
  | "/*" { incr comment_level; comment lexbuf }
  | "*/" { if !comment_level > 0 then (decr comment_level; comment lexbuf) }
  | _ { comment lexbuf }

  and line_comment = parse
  | "\n" { () }
  | _ { line_comment lexbuf }

  and macro = parse
  | "\n" { () }
  | identstart identchar*
    { let s = Lexing.lexeme lexbuf in
      macro_name := s;
      macro lexbuf }
  | int_literal
    { let i = INT (- int_of_string ("-" ^ Lexing.lexeme lexbuf)) in
      Hashtbl.add macro_table !macro_name i }
  | decimal_float_literal
    { let f = FLOAT (Float.of_string (Lexing.lexeme lexbuf)) in
      Hashtbl.add macro_table !macro_name f }
  | _ { macro lexbuf }
{}