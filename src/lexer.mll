{
  open Parser
  open Lexing

  let keyword_table : (string, token) Hashtbl.t = Hashtbl.create 24 ;;
  let () = List.iter (fun (k, t) -> Hashtbl.add keyword_table k t) [
    "type",          TYPE ;
    "forall",        FORALL ;
    "exists",        EXISTS ;
    "Theorem",       THEOREM ;
    "Schema",        SCHEMA ;
    "Specification", SPECIFICATION ;
    "true",          TRUE ;
    "false",         FALSE ;
    "induction",     IND ;
    "apply",         APPLY ;
    "assert",        ASSERT ;
    "case",          CASE ;
    "search",        SEARCH ;
    "to",            TO ;
    "on",            ON ;
    "split",         SPLIT ;
    "left",          LEFT ;
    "right",         RIGHT ;
    "intros",        INTROS ;
    "skip",          SKIP ;
    "abort",         ABORT ;
    "undo",          UNDO ;
    "keep",          KEEP ;
    "Quit",          QUIT ;
    "ctx",           CTX ;
    "o",             OTY ;
    "with",          WITH ;
    "weaken",        WEAKEN ;
    "ctxpermute",    PERMUTECTX ;
    "permute",       PERMUTE ;
    "strengthen",    STRENGTHEN ;
    "inst",          INST ;
    "prune",         PRUNE ;

    "Define",        DEFINE ;
    "prop",          PROP ;
    "unfold",        UNFOLD ;
    "applydfn",      APPDFN ;
    "by",            BY ;

    "Set",           SET ;
    "search_depth",  SEARCHDEPTH ;
  ] ;;

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }

  let comment_level = ref 0
}

let number = ['0'-'9'] +

(* Initial characters for variables *)
let ichar = ['A'-'Z' 'a'-'z' '-' '^' '=' '`' '\'' '?' '$']

(* Characters allowed only in the body of variables. *)
let bchar = ['0'-'9' '_' '/' '*' '@' '+' '#' '!' '&' '~']

let name = ichar (ichar|bchar)*
let blank = ' ' | '\t' | '\r'

rule token = parse
| "/*"               { incr comment_level; comment lexbuf }
| '%' [^'\n']* '\n'? { incrline lexbuf; token lexbuf }

| blank              { token lexbuf }
| '\n'               { incrline lexbuf; token lexbuf }

| '"' ([^ '"']* as s) '"'
                     { QSTRING s }                     
                     
| "=>"               { IMP }
| ":="               { DEFEQ }
| ","                { COMMA }
| "."                { DOT }
| ";"                { SEMICOLON }
| "("                { LPAREN }
| ")"                { RPAREN }
| "|-"               { TURN }
| "="                { EQ }

| ":"                { COLON }
| "->"               { RARROW }
| "<->"              { RLARROW }
| "*"                { STAR }
| "@"                { AT }
| "\\/"              { OR }
| "/\\"              { AND }
| "{"                { LBRACE }
| "}"                { RBRACE }
| "["                { LBRACK }
| "]"                { RBRACK }
| "<"                { LANGLE }
| ">"                { RANGLE }
| number as n        { NUM (int_of_string n) }
| name as id          { try Hashtbl.find keyword_table id
                       with Not_found -> STRINGID id }

| eof                { EOF }

| '\x04'             { EOF }   (* ctrl-D *)

| _                  { failwith ("Illegal character " ^
                                   (Lexing.lexeme lexbuf) ^ " in input") }

and comment = parse
| [^ '*' '/' '\n']+  { comment lexbuf }
| "/*"               { incr comment_level; comment lexbuf }
| "*/"               { decr comment_level ;
                       if !comment_level = 0 then
                         token lexbuf
                       else
                         comment lexbuf }
| "*"                { comment lexbuf }
| "/"                { comment lexbuf }
| "\n"               { incrline lexbuf; comment lexbuf }
| eof                { print_endline
                         "Warning: comment not closed at end of file" ;
                       token lexbuf }
