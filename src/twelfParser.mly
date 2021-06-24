%{
  open Extensions
  open Uterms

  let error_report ?(pos=Parsing.symbol_start_pos ()) fmt =
    let open Lexing in
    let parse_fmt = "@.%s:@\nError: @[" ^^ fmt ^^ "@]@." in
    let pos_string =
      if pos == Lexing.dummy_pos then
        "Unknown position"
      else
        Printf.sprintf "File %S, line %d, character %d"
          pos.pos_fname pos.pos_lnum
          (pos.pos_cnum - pos.pos_bol + 1)
    in
    Format.kfprintf
      (fun _ -> raise Reported_parse_error)
      Format.err_formatter parse_fmt pos_string

  let nested_app head args =
    List.fold_left
      (fun h a -> UApp((fst (get_pos h), snd (get_pos a)), h, a))
      head args
  
  let pos i =
    if i = 0 then
      (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
    else
      (Parsing.rhs_start_pos i, Parsing.rhs_end_pos i)

%}

%token ARROW BACKARROW COLON DOT EQUAL UNDERSCORE
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token TYPE STAR INFIX PREFIX POSTFIX
%token NAME DEFINE SOLVE QUERY FQUERY
%token COMPILE QUERYTABLED MODE UNIQUE
%token COVERS TOTAL TERMINATES BLOCK WORLDS 
%token REDUCES TABLED KEEPTABLE THEOREM PROVE
%token ESTABLISH ASSERT ABBREV TRUSTME FREEZE
%token THAW SUBORD DETERMINISTIC CLAUSE SIG 
%token STRUCT WHERE INCLUDE OPEN USE
%token NONE LEFT RIGHT
%token <int> NUM
%token <string> ID
%token EOF

%nonassoc LOW       
%nonassoc RBRACE RBRACKET
%right BACKARROW
%right ARROW
%nonassoc LBRACE LBRACKET LPAREN TYPE ID
%left APP
       
%start decl
%type <Uterms.sig_decl> decl

%%

id:
| ID { $1 }

/* ids: */
/* | { [] } */
/* | id ids { $1::$2 } */

decl:
| id COLON term DOT
     { Uterms.Const($1, $3) }
/* | adefn DOT */
/*| INFIX ixdecl DOT */
/*     { $2 } */
/*| PREFIX pxdecl DOT */
/*     { let (id, prec) = $2 in */
/*       Uterms.Fixity(id, Signature.Prefix(prec)) } */
/*| POSTFIX pxdecl DOT */
/*     { let (id, prec) = $2 in */
/*       Uterms.Fixity(id, Signature.Postfix(prec)) } */
/* | NAME namepref DOT */
/* | QUERY qdecl DOT */
/* | CLAUSE defn DOT */
/* | sdecl DOT */
/* | TABLED id DOT */
/* | QUERYTABLED qtdecl DOT */
/* | DETREMINISTIC ddecl DOT */
/* | MODE mdecl DOT */
/* | TERMINATES tdecl DOT */
/* | REDUCES rdecl DOT */
/* | BLOCK id COLON bdecl DOT */
/* | WORLDS wdecl DOT */
/* | TOTAL tdecl DOT */
/* | FREEZE ids DOT */
/* | THEOREM thdecl DOT */
/* | PROVE pdecl DOT */
/* | ESTABLISH pdecl DOT */
/* | ASSERT callpats DOT */
/* | USE domain DOT */
| EOF
    { raise End_of_file }

term:
| ground_term
    { $1 }
| term ARROW term
    { Uterms.UPi(pos 0, ((Lexing.dummy_pos, Lexing.dummy_pos),"_"), $1, $3) }
| term BACKARROW term
    { Uterms.UPi(pos 0, ((Lexing.dummy_pos, Lexing.dummy_pos),"_"), $3, $1) }
| LBRACE id COLON term RBRACE term
    { Uterms.UPi(pos 0, (pos 2, $2), $4, $6) }
| LBRACKET id RBRACKET term
    { Uterms.ULam(pos 0, (pos 2, $2, None), $4) }
| term term %prec APP 
    { Uterms.UApp(pos 0, $1, $2) }

ground_term:
| TYPE
    { Uterms.UType(pos 0) }
| id
    { Uterms.UConst(pos 0, $1) }
| LPAREN term RPAREN
    { $2 }
    
  
/* defn: */
/* | id COLON term EQUAL term */
/* | id EQUAL term */

/* adefn: */
/* | adecl */
/* | ABBREV adecl */

/* adecl: */
/* | id COLON term EQUAL term */
/* | id EQUAL term */

/* assoc: */
/* | NONE */
/*    { Signature.None } */
/* | LEFT */
/*    { Signature.Left } */
/* | RIGHT */
/*    { Signature.Right } */

/* prec: */
/* | NUM */
/*     { $1 } */

/* ixdecl: */
/* | assoc prec id */
/*     { Uterms.Fixity($3, Signature.Infix($1, $2)) } */

/* pxdecl: */
/* | prec id */
/*     { ($1, $2) } */

/* sdecl: */
/* | DEFINE binding sdecl */
/* | SOLVE id COLON term */
/* | SOLVE UNDERSCORE COLON term */

/* binding: */
/* | id EQUAL id */
/* | id EQUAL id term */

/* namepref: */
/* | id */
/* | id id */

/* query: */
/* | id COLON term */
/* | term */

/* bound: */
/* | NUM */
/* | STAR */

/* qdecl: */
/* | bound bound query */

/* qtdecl: */
/* | bound bound query */

   
