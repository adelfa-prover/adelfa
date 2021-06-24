{
  open TwelfParser
  open Lexing

  let keyword_table : (string, token) Hashtbl.t = Hashtbl.create 39 ;;
  let () = List.iter (fun (k, t) -> Hashtbl.add keyword_table k t) [
    "%.", EOF ;
    "type", TYPE ;
    "%infix", INFIX ;
    "%prefix", PREFIX ;
    "%postfix", POSTFIX ;
    "%name", NAME ;
    "%define", DEFINE ;
    "%solve", SOLVE ;
    "%query", QUERY ;
    "%fquery", FQUERY ;
    "%compile", COMPILE ;
    "%querytabled", QUERYTABLED ;
    "%mode", MODE ;
    "%unique", UNIQUE ;
    "%covers", COVERS ;
    "%total", TOTAL ;
    "%terminates", TERMINATES ;
    "%block", BLOCK ;
    "%worlds", WORLDS ;
    "%reduces", REDUCES ;
    "%tabled", TABLED ;
    "%keeptable", KEEPTABLE ;
    "%theorem", THEOREM ;
    "%prove", PROVE ;
    "%establish", ESTABLISH ;
    "%assert", ASSERT ;
    "%abbrev", ABBREV ;
    "%trustme", TRUSTME ;
    "%freee", FREEZE ;
    "%thaw", THAW ;
    "%subord", SUBORD ;
    "%deterministic", DETERMINISTIC ;
    "%cluse", CLAUSE ;
    "%sig", SIG ;
    "%struct", STRUCT ;
    "%where", WHERE ;
    "%include", INCLUDE ;
    "%open", OPEN ;
    "%use", USE ;
    "none", NONE ;
    "left", LEFT ;
    "right", RIGHT 
  ] ;;

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }

  let comment_level = ref 0
}

let number = ['0'-'9'] +
  
let char = [^ ':' '.' '(' ')' '[' ']' '{' '}' '%' ' ' '\n' '\t' '\r' '"']
  
let name = char*
let blank = ' ' | '\t' | '\r'

rule token = parse
| eof { EOF }
| "%{" { incr comment_level; comment lexbuf }
| '%' blank [^'\n']* '\n'? {incrline lexbuf; token lexbuf }
| blank { token lexbuf }
| '\n' { incrline lexbuf; token lexbuf }
| "->" { ARROW }
| "<-" { BACKARROW }
| "." { DOT }
| ":" { COLON }
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRACKET }
| "]" { RBRACKET }
| "{" { LBRACE }
| "}" { RBRACE }
| "=" { EQUAL }
| "*" { STAR }
| number as n { NUM (int_of_string n) }
| name as id { try Hashtbl.find keyword_table id
                with Not_found -> ID id }
| "_" { UNDERSCORE }
| _ { failwith ("Illegal character " ^
                   (Lexing.lexeme lexbuf) ^ " in input") }

and comment = parse
| [^ '%' '{' '\n']+ { comment lexbuf }
| "%{" { incr comment_level; comment lexbuf }
| "}%" { decr comment_level ;
         if !comment_level = 0 then
           token lexbuf
         else
           comment lexbuf }
| "%" { comment lexbuf }
| "{" { comment lexbuf }
| "\n" { incrline lexbuf; comment lexbuf }
| eof { print_endline
          "Warning: comment not closed at end of file" ;
        token lexbuf }
