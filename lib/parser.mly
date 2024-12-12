%{
open Ast

(* exception NonPrimPvtElementTypeOfZkRam of typ *)

let mk_p_expr_node pe =
  { p_expr = pe;
    p_expr_loc = Location.symbol_rloc ();
  }
let mk_p_cmd_node pc =
  { p_cmd = pc;
    p_cmd_loc = Location.symbol_rloc ();
  }
let p_skip_node = { p_cmd = PCskip; p_cmd_loc = Location.none }

let constant_table =
  let tbl = Hashtbl.create 20 in
  (* Hashtbl.add tbl "true" Etrue;
  Hashtbl.add tbl "false" Efalse; *)
  tbl
%}

%token EOF
%token <int> INT
%token <float> FLOAT
%token NULL
%token TINT
%token TBOOL
%token TFLOAT
%token TUNIT
%token STRUCT
%token PRIVATE
%token PUBLIC
%token PLOCAL
%token PRIVATE1
%token PRIVATE2
%token PUBLIC0
%token PUBLIC1
%token PUBLIC2
%token PLOCAL1
%token PLOCAL2
(*
%token KNW0
%token KNW1
%token KNW2
*)
%token DECLARE
%token ATOMIC_ANNO
%token PLOCAL1_ANNO
%token PLOCAL2_ANNO
%token BLACKBOX1_ANNO
%token BLACKBOX2_ANNO
%token ASSIGN
%token TRUE
%token FALSE
%token ADD
%token SUB
%token MUL (* also DEREF *)
%token DIV
%token MOD
%token EQ
%token NE
%token GE
%token GT
%token LE
%token LT
%token AND
%token OR
%token NOT
%token LAND (* also REF *)
%token LOR
%token LXOR
%token LNOT
%token LSL
%token LSR
%token IF
%token ELSE
%token WHILE
%token FOR
%token RETURN
%token BREAK
%token CONTINUE
%token ASSERT
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
%token SEMICOLON
%token COMMA
%token DOT
%token RARROW
%token <string> IDENT

/* command level precedences */
// %nonassoc below_SEQ
// %nonassoc SEMICOLON
// %nonassoc ASSIGN
// %nonassoc ELSE

/* reference: https://en.cppreference.com/w/c/language/operator_precedence */
/* expression level precedences */
%left OR
%left AND
%left LOR
%left LXOR
%left LAND
%nonassoc EQ NE LT LE GE GT
%left LSL LSR
%left ADD SUB
%left MUL DIV MOD
%right UNOP
%left LBRACKET DOT RARROW

%start protocol_entry
%type<(Ast.p_top list)> protocol_entry

%%
protocol_entry:
  | tops EOF { $1 }
;

expression:
  | TRUE { mk_p_expr_node (PEbool true) }
  | FALSE { mk_p_expr_node (PEbool false) }
  | INT { mk_p_expr_node (PEint $1) }
  | FLOAT { mk_p_expr_node (PEfloat $1) }
  | NULL { mk_p_expr_node PEnull }
  | IDENT {
    try Hashtbl.find constant_table $1
    with Not_found -> mk_p_expr_node (PEvar $1) }
  | expression LBRACKET expression RBRACKET { mk_p_expr_node (PEindex ($1, $3)) }
  | expression DOT IDENT { mk_p_expr_node (PEfield ($1, $3)) }
  | expression RARROW IDENT
  { let base = { p_expr = PEderef $1; p_expr_loc = Location.rhs_loc 1 } in
    mk_p_expr_node (PEfield (base, $3)) }
  | MUL expression %prec UNOP { mk_p_expr_node (PEderef $2) }
  | IDENT LPAREN arguments RPAREN { mk_p_expr_node (PEcall ($1, $3)) }
  | LAND expression %prec UNOP { mk_p_expr_node (PEref $2) }
  | SUB expression %prec UNOP { mk_p_expr_node (PEunary (Oneg, $2)) }
  | NOT expression %prec UNOP { mk_p_expr_node (PEunary (Onot, $2)) }
  | LNOT expression %prec UNOP { mk_p_expr_node (PEunary (Olnot, $2)) }
  | expression ADD expression { mk_p_expr_node (PEbinary ($1, Oadd, $3)) }
  | expression SUB expression { mk_p_expr_node (PEbinary ($1, Osub, $3)) }
  | expression MUL expression { mk_p_expr_node (PEbinary ($1, Omul, $3)) }
  | expression DIV expression { mk_p_expr_node (PEbinary ($1, Odiv, $3)) }
  | expression MOD expression { mk_p_expr_node (PEbinary ($1, Omod, $3)) }
  | expression AND expression { mk_p_expr_node (PEbinary ($1, Oand, $3)) }
  | expression OR expression { mk_p_expr_node (PEbinary ($1, Oor, $3)) }
  | expression EQ expression { mk_p_expr_node (PEbinary ($1, Oeq, $3)) }
  | expression NE expression { mk_p_expr_node (PEbinary ($1, One, $3)) }
  | expression GE expression { mk_p_expr_node (PEbinary ($1, Oge, $3)) }
  | expression GT expression { mk_p_expr_node (PEbinary ($1, Ogt, $3)) }
  | expression LE expression { mk_p_expr_node (PEbinary ($1, Ole, $3)) }
  | expression LT expression { mk_p_expr_node (PEbinary ($1, Olt, $3)) }
  | expression LAND expression { mk_p_expr_node (PEbinary ($1, Oland, $3)) }
  | expression LOR expression { mk_p_expr_node (PEbinary ($1, Olor, $3)) }
  | expression LXOR expression { mk_p_expr_node (PEbinary ($1, Olxor, $3)) }
  | expression LSL expression { mk_p_expr_node (PEbinary ($1, Olsl, $3)) }
  | expression LSR expression { mk_p_expr_node (PEbinary ($1, Olsr, $3)) }
  | LPAREN expression RPAREN { $2 }
  | LBRACE expressions_nonempty RBRACE { mk_p_expr_node (PEarrayinit $2) }
  /* | ARRAY LPAREN expression COMMA expression RPAREN { mk_p_expr_node (PEarrayinit ($3, $5)) } */
  | LBRACE field_assignments_nonempty RBRACE { mk_p_expr_node (PEstructinit $2) }
;

expressions_nonempty:
  | expression { [$1] }
  | expression COMMA expressions_nonempty { $1 :: $3 }
;
field_assignment:
  | DOT IDENT ASSIGN expression { ($2, $4) }
;
field_assignments_nonempty:
  | field_assignment { [$1] }
  | field_assignment COMMA field_assignments_nonempty { $1 :: $3 }
;

security_level:
  | { Public K0Public }
  | PUBLIC { Public K0Public }
  | PUBLIC0 { Public K0Public }
  | PUBLIC1 { Public K1Public }
  | PUBLIC2 { Public K2Public }
  | PRIVATE { Private K1Private }
  | PRIVATE1 { Private K1Private }
  | PRIVATE2 { Private K2Private }
  | PLOCAL { Plocal K1Plocal }
  | PLOCAL1 { Plocal K1Plocal }
  | PLOCAL2 { Plocal K2Plocal }
;

atom_type_expression:
  | TUNIT { Tunit }
  | security_level TINT { Tint $1 }
  | security_level TBOOL { Tbool $1 }
  | security_level TFLOAT { Tfloat $1 }
  | type_expression MUL { Tref $1 }
;
type_expression:
  | atom_type_expression { $1 }
  | type_expression LBRACKET security_level INT RBRACKET { Tarray ($1, $3, $4) }
  | STRUCT IDENT { Tstruct $2 }
  | LPAREN type_expression RPAREN { $2 }
;

commands_nonempty:
  | command { $1 }
  | command commands_nonempty { mk_p_cmd_node (PCseq ($1, $2)) }
;
commands:
  | { p_skip_node }
  | commands_nonempty { $1 }
;
command:
  | LBRACE commands RBRACE { mk_p_cmd_node (PCsection $2) }
  | expression ASSIGN expression SEMICOLON { mk_p_cmd_node (PCasgn ($1, $3)) }
  | expression SEMICOLON { mk_p_cmd_node (PCeval $1) }
  | type_expression IDENT ASSIGN expression SEMICOLON
  { mk_p_cmd_node (PCdef ($1, $2, $4)) }
  | IF expression LBRACE commands RBRACE
  { let c1 = { p_cmd = PCsection $4; p_cmd_loc = Location.rhs_interval 3 5 } in
    let c2 = { p_cmd = PCsection p_skip_node; p_cmd_loc = Location.none } in
    mk_p_cmd_node (PCif ($2, c1, c2)) }
  | IF expression LBRACE commands RBRACE ELSE LBRACE commands RBRACE
  { let c1 = { p_cmd = PCsection $4; p_cmd_loc = Location.rhs_interval 3 5 } in
    let c2 = { p_cmd = PCsection $8; p_cmd_loc = Location.rhs_interval 7 9 } in
    mk_p_cmd_node (PCif ($2, c1, c2)) }
  | WHILE expression LBRACE commands RBRACE
  { let body = { p_cmd = PCsection $4; p_cmd_loc = Location.rhs_interval 3 5 } in
    mk_p_cmd_node (PCwhile ($2, body)) }
  | FOR command expression SEMICOLON command LBRACE commands RBRACE
  { mk_p_cmd_node (PCfor ($2, $3, $5, $7)) }
  | RETURN expression SEMICOLON { mk_p_cmd_node (PCreturn $2) }
  | RETURN SEMICOLON
  { let ret = { p_expr = PEunit; p_expr_loc = Location.rhs_loc 2 } in
    mk_p_cmd_node (PCreturn ret) }
  | BREAK SEMICOLON { mk_p_cmd_node PCbreak }
  | CONTINUE SEMICOLON { mk_p_cmd_node PCcontinue }
  | ASSERT expression SEMICOLON { mk_p_cmd_node (PCassert $2) }
;

field_definition:
  | type_expression IDENT SEMICOLON { ($1, $2) }
;
field_definitions_nonempty:
  | field_definition { [$1] }
  | field_definition field_definitions_nonempty { $1 :: $2 }
;

struct_definition:
  | STRUCT IDENT LBRACE field_definitions_nonempty RBRACE
  { let sd = {
      pstruct_name = $2;
      pstruct_fields = $4; } in
    { p_structdef = sd;
      p_structdef_loc = Location.symbol_rloc (); } }
;

globvar_definition:
  | type_expression IDENT ASSIGN expression SEMICOLON
  { let vd = {
      pgvar_typ = $1;
      pgvar_name = $2;
      pgvar_init = $4; } in
    { p_gvardef = vd;
      p_gvardef_loc = Location.symbol_rloc (); } }
;

arguments_nonempty:
  | expression { [$1] }
  | expression COMMA arguments_nonempty { $1 :: $3 }
;
arguments:
  | { [] }
  | arguments_nonempty { $1 }
;

parameter:
  | type_expression IDENT { ($1, $2, CCval) }
  | type_expression LAND IDENT { ($1, $3, CCref) }
;
parameters_nonempty:
  | parameter { [$1] }
  | parameter COMMA parameters_nonempty { $1 :: $3 }
;
parameters:
  | { [] }
  | parameters_nonempty { $1 }
;

unnamed_parameter:
  | type_expression { ($1, CCval) }
  | type_expression LAND { ($1, CCref) }
;
unnamed_parameters_nonempty:
  | unnamed_parameter { [$1] }
  | unnamed_parameter COMMA unnamed_parameters_nonempty { $1 :: $3 }
;
unnamed_parameters:
  | { [] }
  | unnamed_parameters_nonempty { $1 }
;

raw_function_definition:
  | type_expression IDENT LPAREN parameters RPAREN LBRACE commands RBRACE
  { { pfun_anno = NORMAL;
      pfun_ret_typ = $1;
      pfun_name = $2;
      pfun_params = $4;
      pfun_body = $7; } }
;

function_definition:
  | raw_function_definition
  { { p_fundef = $1;
      p_fundef_loc = Location.symbol_rloc (); } }
  | ATOMIC_ANNO raw_function_definition
  { { p_fundef = {$2 with pfun_anno = ATOMIC };
      p_fundef_loc = Location.symbol_rloc (); } }
  | BLACKBOX1_ANNO raw_function_definition
  { { p_fundef = {$2 with pfun_anno = SANDBOX BLACKBOX1 };
      p_fundef_loc = Location.symbol_rloc (); }}
  | BLACKBOX2_ANNO raw_function_definition
  { { p_fundef = {$2 with pfun_anno = SANDBOX BLACKBOX2 };
      p_fundef_loc = Location.symbol_rloc (); }}
  | PLOCAL1_ANNO raw_function_definition
  { { p_fundef = {$2 with pfun_anno = SANDBOX PLOCAL1 };
      p_fundef_loc = Location.symbol_rloc (); }}
  | PLOCAL2_ANNO raw_function_definition
  { { p_fundef = {$2 with pfun_anno = SANDBOX PLOCAL2 };
      p_fundef_loc = Location.symbol_rloc (); }}
;

external_function_declaration:
  | PLOCAL1_ANNO type_expression IDENT LPAREN unnamed_parameters RPAREN
  { let xd = {
      pxfun_ret_typ = $2;
      pxfun_name = $3;
      pxfun_params = $5;
      pxfun_anno = SANDBOX PLOCAL1; }
    in
    { p_xfundecl = xd;
      p_xfundecl_loc = Location.symbol_rloc (); } }
  | PLOCAL2_ANNO type_expression IDENT LPAREN unnamed_parameters RPAREN
  { let xd = {
      pxfun_ret_typ = $2;
      pxfun_name = $3;
      pxfun_params = $5;
      pxfun_anno = SANDBOX PLOCAL2; }
    in
    { p_xfundecl = xd;
      p_xfundecl_loc = Location.symbol_rloc (); } }
;

tops:
  | { [] }
  | function_definition tops { PTfundef $1 :: $2 }
  | struct_definition tops { PTstructdef $1 :: $2 }
  | globvar_definition tops { PTgvardef $1 :: $2 }
  | DECLARE external_function_declaration tops { PTxfundecl $2 :: $3 }
;

%%