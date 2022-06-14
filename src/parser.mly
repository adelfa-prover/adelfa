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

  let pos i =
    if i = 0 then
      (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
    else
      (Parsing.rhs_start_pos i, Parsing.rhs_end_pos i)

  let predefined id =
    UConst(pos 0, id)

  let binop id t1 t2 =
    UApp(pos 0, UApp(pos 0, predefined id, t1), t2)

  let nested_app head args =
    List.fold_left
      (fun h a -> UApp((fst (get_pos h), snd (get_pos a)), h, a))
      head args

  let nominal_constant_re = Str.regexp "n[0-9]+"
  let is_illegal_constant k =
    Str.string_match nominal_constant_re k 0

  let check_legal_var vid vnum =
    if is_illegal_constant vid then
      error_report ~pos:(Parsing.rhs_start_pos vnum)
        "Invalid bound variable %S.@\nIdentifiers matching n[0-9]+ are reserved for nominal constants." vid

  let deloc_id (_,id) =
    (* if is_illegal_constant id then *)
    (*   error_report ~pos *)
    (*     "Invalid bound variable %S.@\nIdentifiers matching n[0-9]+ are reserved for nominal constants." *)
    (*     id ; *)
    id

  let deloc_id_ty (lid, ty) = (deloc_id lid, ty)

  let check_legal_idterm = function
    | Uterms.UConst _ -> ()
    | utm ->
       error_report
         ~pos:(snd (Uterms.get_pos utm))
         "Invalid term %S.@\nMust be an identifier on left hand side." (Print.string_of_uterm utm)
%}                     

%token IMP COMMA DOT LPAREN RPAREN TURN EQ TRUE FALSE DEFEQ
%token UNFOLD APPDFN
%token APPLY IND CASE SEARCH TO ON INTROS ASSERT WITH PRUNE
%token SKIP ABORT UNDO LEFT RIGHT WEAKEN PERMUTECTX STRENGTHEN INST
%token SPLIT KEEP SPECIFICATION SEMICOLON
%token THEOREM SCHEMA DEFINE
%token QUIT
%token COLON RARROW CTX FORALL EXISTS STAR AT BY
%token OR AND
%token LBRACE RBRACE LBRACK RBRACK LANGLE RANGLE
%token TYPE OTY PROP
       
%token <int> NUM
%token <string> STRINGID QSTRING
%token EOF                               

%nonassoc COMMA
%right IMP
%left OR
%left AND
%nonassoc RBRACE RBRACK
%right RARROW
       
%start top_command command
%type <Uterms.command> command
%type <Uterms.top_command> top_command

%%

hyp:
  | STRINGID
/* { check_legal_var $1 1 ; $1 } */
   { $1 }

loc_id:
  | id
    { (pos 0, $1) }

id:
  | STRINGID      { $1 }
  | IND           { "induction" }
  | APPLY         { "apply" }
  | CASE          { "case" }
  | SEARCH        { "search" }
  | ON            { "on" }
  | INTROS        { "intros" }
  | ASSERT        { "assert" }
  | SKIP          { "skip" }
  | UNDO          { "undo" }
  | LEFT          { "left" }
  | RIGHT         { "right" }
  | SPLIT         { "split" }
  | KEEP          { "keep" }
  | THEOREM       { "Theorem" }
  | SPECIFICATION { "Specification" }
  | SCHEMA        { "Schema" }
  | QUIT          { "Quit" }
  | DEFINE        { "Define" }
  | BY            { "by" }
                  
id_list:
  | loc_id
    { [(pos 0, deloc_id $1)] }
  | loc_id id_list
    { (pos 1,deloc_id $1)::$2 }

aid:
  | term COLON term
    { check_legal_idterm $1;
      let pos, id = match $1 with
        | Uterms.UConst (pos, id) -> (pos, id)
        | _ -> bugf "Expected constant"
      in
      ((pos,id), $3)
    }

aid_list:
  | aid COMMA aid_list
    { let (id,ty) = $1 in
      let id = deloc_id id in
      (pos 1,id,ty)::$3 }
  | aid
    { let (id,ty) = $1 in
      let id = deloc_id id in
      [(pos 1,id,ty)] }

basety:
  | LPAREN ty RPAREN
      { $2 }
  | OTY
      { Type.oty }
    
ty:
  | basety
      { $1 }
  | ty RARROW ty
      { Type.tyarrow [$1] $3 }

propty:
  | PROP
      { Type.propty }
  | ty RARROW PROP
      { Type.tyarrow [$1]  Type.propty }

term:
  | LBRACE aid RBRACE term
    { let (id,ty) = $2 in
      Uterms.UPi(pos 0, id, ty, $4) }
  | term RARROW term
    { Uterms.UPi(pos 0, ((Lexing.dummy_pos, Lexing.dummy_pos), "_"),$1,$3) }
  | LBRACK idty RBRACK term
    { let (p, (id,tyopt)) = $2 in
      Uterms.ULam(pos 0, (p,id,tyopt), $4) }
  | TYPE
    { Uterms.UType (pos 0)}
  | exp
    { $1 }
  | exp exp_list
    { nested_app $1 $2 }

exp:
  | LPAREN term RPAREN
    { let left = fst (pos 1) in
      let right = snd (pos 3) in
      change_pos (left,right) $2 }
  | loc_id
    { Uterms.UConst(pos 0, deloc_id $1) }

exp_list:
  | exp exp_list
    { ($1::$2) }
  | exp
    { [$1] }    
    
defs:
  | def SEMICOLON defs
    { ($1::$3) }
  | def
    { [$1] }

def:
  | formula DEFEQ formula
    { ($1, $3) }
  | formula
    { ($1, Uterms.UTop) }
    
clearable:
  | hyp
    { Uterms.Keep $1 }
  | STAR hyp
    { Uterms.Remove $2 }

apply_arg:
  | hyp
    { Uterms.Keep $1 }
  | STAR STRINGID
/* { check_legal_var $2 2 ; Uterms.Remove $2 } */
    { Uterms.Remove $2 }

apply_args:
  | apply_arg apply_args
    { $1::$2 }
  | apply_arg
    { [$1] }

command:
  | IND ON NUM DOT
    { Uterms.Ind($3) }
  | APPLY clearable TO apply_args WITH withs DOT
    { Uterms.Apply($2, $4, $6) }
  | APPLY clearable TO apply_args DOT
    { Uterms.Apply($2, $4, []) }
  | APPLY clearable WITH withs DOT
    { Uterms.Apply($2, [], $4) }
  | ASSERT formula DOT
    { Uterms.Assert($2) }
  | CASE hyp DOT
    { Uterms.Case(Uterms.Remove $2) }
  | CASE hyp LPAREN KEEP RPAREN DOT
    { Uterms.Case(Uterms.Keep $2) }
  | EXISTS term DOT
    { Uterms.Exists($2) }
  | SEARCH DOT
    { Uterms.Search(Uterms.DefaultDepth) }
  | SEARCH NUM DOT
    { Uterms.Search(Uterms.WithDepth($2)) }
  | SPLIT DOT
    { Uterms.Split }
  | LEFT DOT
    { Uterms.Left }
  | RIGHT DOT
    { Uterms.Right }
  | INTROS DOT
    { Uterms.Intros }
  | SKIP DOT
    { Uterms.Skip }
  | ABORT DOT
    { Uterms.Abort }
  | UNDO DOT
    { Uterms.Undo }
  | WEAKEN clearable WITH term DOT
      { Uterms.Weaken($2, $4, Uterms.DefaultDepth) }
  | WEAKEN clearable WITH term NUM DOT
      { Uterms.Weaken($2, $4, Uterms.WithDepth($5)) }
  | PERMUTECTX clearable TO context_expr DOT 
      { Uterms.PermuteCtx($2, $4) }
  | STRENGTHEN clearable DOT
      { Uterms.Strengthen($2) }
  | INST clearable WITH id EQ term DOT
      { Uterms.Inst($2, [Uterms.Vws($4,$6)], Uterms.DefaultDepth) }
  | INST clearable WITH id EQ term NUM DOT
      { Uterms.Inst($2, [Uterms.Vws($4,$6)], Uterms.WithDepth($7)) }
  | PRUNE hyp DOT
      { Uterms.Prune($2) }
  | UNFOLD hyp WITH withs DOT
      { Uterms.Unfold(Some $2, $4) }
  | UNFOLD WITH withs DOT
      { Uterms.Unfold(None, $3) }
  | UNFOLD hyp DOT
      { Uterms.Unfold(Some $2, []) }
  | UNFOLD DOT
      { Uterms.Unfold(None, []) }
  | APPDFN id TO id WITH withs DOT
      { Uterms.AppDfn($2,Some $4, $6) }
  | APPDFN id WITH withs DOT
      { Uterms.AppDfn($2, None, $4) }
  | APPDFN id TO id DOT
      { Uterms.AppDfn($2,Some $4, []) }
  | APPDFN id DOT
      { Uterms.AppDfn($2, None, []) }

ctxbinding:
  | loc_id COLON loc_id
    { (pos 0, deloc_id $1, deloc_id $3) }

ctxbinding_list:
  | ctxbinding ctxbinding_list
    { $1::$2 }
  | ctxbinding
    { [$1] }

context_expr:
  | loc_id
    { Uterms.UVar(pos 0, deloc_id $1) }
  | context_expr COMMA aid
    { let (id,ty) = $3 in
      let id = deloc_id id in
      Uterms.UCtxTm(pos 3, $1,(id,ty)) }
  | aid
    { let (id,ty) = $1 in
      let id = deloc_id id in
      Uterms.UCtxTm(pos 0,Uterms.UNil (pos 0), (id,ty)) }
  | { Uterms.UNil (pos 0) }

annotation:
  | ats
    { Formula.EQ $1 }
  | stars
    { Formula.LT $1 }
  | { Formula.None }

stars:
  | STAR stars
    { 1 + $2 }
  | STAR
    { 1 }

ats:
  | AT ats
    { 1 + $2 }
  | AT
    { 1 }

idty:
  | loc_id COLON ty
      { (pos 1,(deloc_id $1,Some $3)) }
  | loc_id
      { (pos 1,(deloc_id $1,None)) }
    
idty_list:
  | LPAREN idty RPAREN idty_list
      {$2::$4}
  | idty idty_list
      {$1::$2}
  | idty
      {[$1]}
withs:
  | id EQ term COMMA withs
      { (Uterms.Vws($1,$3)) :: $5 }
  | LPAREN id EQ context_expr RPAREN COMMA withs
      { (Uterms.Cws($2,$4)) :: $7 }
  | id EQ term
      { [Uterms.Vws($1,$3)] }
  | LPAREN id EQ context_expr RPAREN
      { [Uterms.Cws($2,$4)] }
      
formula:
  | term
    { Uterms.UProp($1) }
  | TRUE
    { Uterms.UTop }
  | FALSE
    { Uterms.UBottom }
  | FORALL idty_list COMMA formula
    { Uterms.UAll($2,$4) }
  | EXISTS idty_list COMMA formula
    { Uterms.UExists($2,$4) }
  | CTX ctxbinding_list COMMA formula
    { Uterms.UCtx($2,$4) }
  | formula IMP formula
    { Uterms.UImp($1,$3) }
  | formula AND formula
    { Uterms.UAnd($1,$3) }
  | formula OR formula
    { Uterms.UOr($1,$3) }
  | LBRACE context_expr TURN term COLON term RBRACE annotation
    { Uterms.UAtm($2,$4,$6,$8) }
  | LBRACE term COLON term RBRACE annotation
    { Uterms.UAtm(UNil(pos 0),$2,$4,$6) }
  | LPAREN formula RPAREN
    { $2 }
      
block:
  | LBRACE id_list RBRACE LPAREN aid_list RPAREN
      { ($2,$5) }
  | LPAREN aid_list RPAREN
      { ([],$2) }

block_list:
  | block SEMICOLON block_list
    { $1::$3 }
  | block
    { [$1] }

top_command:
  | THEOREM loc_id COLON formula DOT
    { Uterms.Theorem(deloc_id $2, $4) }
  | DEFINE term COLON propty BY defs DOT
    { check_legal_idterm $2;
      Uterms.Define((Uterms.get_const_id $2, Some $4), $6) }
  | SCHEMA loc_id DEFEQ block_list DOT
    { Uterms.Schema(deloc_id $2, $4) }
  | SPECIFICATION QSTRING DOT
    { Uterms.Specification($2) }
  | QUIT DOT
    { Uterms.Quit }       
  | EOF
    { raise End_of_file }      
                             
                             
