(* Implements the main interaction loop of the system. *)
open Extensions
open Printf

let welcome_message = "Welcome!"
let exit_message = "Goodbye!"
let interactive = ref true
let out = ref stdout
let switch_to_interactive = ref false
let lexbuf = ref (Lexing.from_channel stdin)
let count = ref 0
let inputFile = ref ""

let perform_switch_to_interactive () =
  assert !switch_to_interactive;
  switch_to_interactive := false;
  lexbuf := Lexing.from_channel stdin;
  interactive := true;
  fprintf stdout "Switching to interactive mode.\n%!"
;;

let interactive_or_exit () =
  if not !interactive
  then if !switch_to_interactive then perform_switch_to_interactive () else exit 1
;;

(* if interactive, reset line count to provide
   more accurate error position information. *)
let reset_if_interactive () =
  if !interactive
  then
    !lexbuf.lex_curr_p
      <- { !lexbuf.lex_curr_p with pos_cnum = 0; pos_bol = 0; pos_lnum = 1 }
;;

(* Lexing.flush_input !lexbuf; *)

let position_range (p1, p2) =
  let file = p1.Lexing.pos_fname in
  let line = p1.Lexing.pos_lnum in
  let char1 = p1.Lexing.pos_cnum - p1.Lexing.pos_bol in
  let char2 = p2.Lexing.pos_cnum - p1.Lexing.pos_bol in
  if file = ""
  then (* "" *)
    sprintf ": line %d, characters %d-%d" line char1 char2
  else sprintf ": file %s, line %d, characters %d-%d" file line char1 char2
;;

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  if file = ""
  then
    (* "" (\* lexbuf information is rarely accurate at the toplevel *\) *)
    sprintf ": line %d, character %d" line char
  else sprintf ": file %s, line %d, character %d" file line char
;;

let setInputFile name =
  if !inputFile = ""
  then (
    inputFile := name;
    interactive := false)
  else failwith "Error: More than one input file specified."
;;

let checkInput () =
  if !inputFile = "" && !interactive
  then ()
  else if Sys.file_exists !inputFile
  then (
    lexbuf := Lexing.from_channel (open_in !inputFile);
    !lexbuf.Lexing.lex_curr_p
      <- { !lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = !inputFile })
  else failwith ("Error: Invalid input file: `" ^ !inputFile ^ "'.")
;;

let usageMsg = "Usage: main [options]\n" ^ "options are: "

let specList =
  [ "-i", Arg.String setInputFile, " Specifies a file from which to read input."
  ; "--input", Arg.String setInputFile, " Specifies a file from which to read input."
  ; "-a", Arg.Set Globals.annotate, " Annotate mode"
  ]
;;

let parse_args () = Arg.parse specList (fun _ -> ()) usageMsg

let print_top_prompt () =
  print_string ">> ";
  flush stdout
;;

let print_proof_prompt () =
  let thm_name = (Prover.get_sequent ()).name in
  print_string (thm_name ^ ">> ");
  flush stdout
;;

let read_spec filename =
  let inchan = open_in filename in
  let lexbuf = Lexing.from_channel inchan in
  try
    while true do
      let udecl = TwelfParser.decl TwelfLexer.token lexbuf in
      match udecl with
      | Uterms.Const (id, utm) ->
        let tm, _ = Translate.trans_term !Prover.lf_sig [] [] [] [] (Some Type.oty) utm in
        if Term.is_kind tm
        then (
          let tydecl = Signature.ty_dec id tm 0 Signature.NoFixity [] in
          Prover.set_sig (Signature.add_type_decl !Prover.lf_sig tydecl))
        else (
          let odecl = Signature.obj_dec id tm 0 Signature.NoFixity in
          Prover.set_sig (Signature.add_obj_decl !Prover.lf_sig odecl))
      | Fixity _ -> bugf "Expected const reading specification"
    done
  with
  | End_of_file ->
    close_in inchan;
    ()
;;

(* process proof tactics for deriving the current theorem.
   Read from a file or stdin *)
let process_proof () =
  (* read in tactic, call appropriate step in prover.
       if proof complete is raised return to outer loop. *)
  if !Globals.annotate
  then (
    fprintf !out "</pre>\n%!";
    incr count;
    fprintf !out "<a name=\"%d\"></a>\n%!" !count;
    fprintf !out "<pre>\n%!");
  print_proof_prompt ();
  let input = Parser.command Lexer.token !lexbuf in
  if not !interactive
  then (
    let pre, post = if !Globals.annotate then "<b>", "</b>" else "", "" in
    fprintf !out "%s%s%s\n%!" pre (Print.string_of_command input) post);
  match input with
  | Uterms.Abort -> raise End_of_file
  | Uterms.Skip -> Prover.skip ()
  | Uterms.Undo -> Prover.undo ()
  | Uterms.Search depth -> Prover.search depth ()
  | Uterms.Ind i ->
    (try Prover.induction i with
    | Tactics.InvalidFormula (_, str) -> prerr_endline str)
  | Uterms.Apply (Uterms.Keep name, args, withs)
  | Uterms.Apply (Uterms.Remove name, args, withs) ->
    (* we don't currently remove hyps so treat the same *)
    Prover.apply
      name
      (List.map
         (fun x ->
           match x with
           | Uterms.Keep arg | Uterms.Remove arg -> arg)
         args)
      withs
  | Uterms.Case (Uterms.Keep hyp) -> Prover.case false hyp
  | Uterms.Case (Uterms.Remove hyp) -> Prover.case true hyp
  | Uterms.Exists utm ->
    (* weak type checking/inference must be done on utm using current proof state
           then call Prover.exsits*)
    let nvars =
      List.filter
        (fun (_, t) -> Term.is_var Term.Nominal t)
        (Prover.get_sequent ()).Sequent.vars
    in
    let evars =
      List.filter
        (fun (_, t) -> Term.is_var Term.Eigen t)
        (Prover.get_sequent ()).Sequent.vars
    in
    (match (Prover.get_sequent ()).goal with
    | Formula.Exists ((_, ty) :: _, _) ->
      let term, _ =
        Translate.trans_term
          !Prover.lf_sig
          (List.map (fun (id, t) -> id, ref (Some t)) evars)
          []
          (List.map (fun (id, t) -> id, ref (Some t)) nvars)
          []
          (Some ty)
          utm
      in
      Prover.exists term
    | _ -> prerr_endline "Goal formula not existential")
  | Uterms.Split -> Prover.split ()
  | Uterms.Left -> Prover.left ()
  | Uterms.Right -> Prover.right ()
  | Uterms.Intros -> Prover.intros ()
  | Uterms.Assert uform ->
    (* weak type inf. on formula. then call Prover.cut *)
    let nvars =
      List.filter
        (fun (_, t) -> Term.is_var Term.Nominal t)
        (Prover.get_sequent ()).Sequent.vars
    in
    let evars =
      List.filter
        (fun (_, t) -> Term.is_var Term.Eigen t)
        (Prover.get_sequent ()).Sequent.vars
    in
    let nvar_ctx = List.map (fun (id, t) -> id, ref (Some t)) nvars in
    let evar_ctx = List.map (fun (id, t) -> id, ref (Some t)) evars in
    let form =
      Translate.trans_formula
        !Prover.lf_sig
        !Prover.schemas
        (Prover.get_propty_lst ())
        evar_ctx
        []
        (Prover.get_sequent ()).Sequent.ctxvars
        nvar_ctx
        uform
    in
    Prover.assert_thm form
  | Uterms.Weaken (clear, utm, depth) ->
    let nvars =
      List.filter
        (fun (_, t) -> Term.is_var Term.Nominal t)
        (Prover.get_sequent ()).Sequent.vars
    in
    let evars =
      List.filter
        (fun (_, t) -> Term.is_var Term.Eigen t)
        (Prover.get_sequent ()).Sequent.vars
    in
    let t, _ =
      Translate.trans_term
        !Prover.lf_sig
        (List.map (fun (id, t) -> id, ref (Some t)) evars)
        []
        (List.map (fun (id, t) -> id, ref (Some t)) nvars)
        []
        (Some Type.oty)
        utm
    in
    (match clear with
    | Uterms.Keep name -> Prover.weaken depth false name t
    | Uterms.Remove name -> Prover.weaken depth true name t)
  | Uterms.PermuteCtx (clear, uctx) ->
    let nvars =
      List.filter
        (fun (_, t) -> Term.is_var Term.Nominal t)
        (Prover.get_sequent ()).Sequent.vars
    in
    let evars =
      List.filter
        (fun (_, t) -> Term.is_var Term.Eigen t)
        (Prover.get_sequent ()).Sequent.vars
    in
    let nvar_ctx = List.map (fun (id, t) -> id, ref (Some t)) nvars in
    let evar_ctx = List.map (fun (id, t) -> id, ref (Some t)) evars in
    let g, _ =
      Translate.trans_ctx
        !Prover.lf_sig
        evar_ctx
        []
        (Prover.get_sequent ()).Sequent.ctxvars
        nvar_ctx
        uctx
    in
    (match clear with
    | Uterms.Keep name -> Prover.permute_ctx false name g
    | Uterms.Remove name -> Prover.permute_ctx true name g)
  | Uterms.Strengthen clear ->
    (match clear with
    | Uterms.Keep name -> Prover.strengthen false name
    | Uterms.Remove name -> Prover.strengthen true name)
  | Uterms.Inst (clear, uwiths, depth) ->
    (match clear with
    | Uterms.Keep name -> Prover.inst depth false name uwiths
    | Uterms.Remove name -> Prover.inst depth true name uwiths)
  | Uterms.Prune id -> Prover.prune id
  | Uterms.Unfold (hypnameop, withs) -> Prover.unfold hypnameop withs
  | Uterms.AppDfn (defname, hypnameop, withs) -> Prover.applydfn defname hypnameop withs
;;

let rec proof_loop () =
  while true do
    reset_if_interactive ();
    (try
       process_proof ();
       Sequent.normalize_hyps (Prover.get_sequent ())
     with
    | Parsing.Parse_error ->
      eprintf "Syntax error%s.\n%!" (position !lexbuf);
      Lexing.flush_input !lexbuf;
      interactive_or_exit ()
    | Translate.TypingError e ->
      eprintf "Typing error%s.\n%!" (position_range (Translate.get_error_pos e));
      eprintf "%s.\n%!" (Translate.explain_error e);
      interactive_or_exit ()
    | Failure s ->
      eprintf "Failure:%s\n%!" s;
      interactive_or_exit ());
    Prover.display_state ();
    proof_loop ()
  done
;;

(* Process toplevel commands;
   either from file or interactive *)
let process () =
  (* parse top-level command from stdin, or file *)
  (* if no LF signature loaded, error on any other commands *)
  (* if a theorem is stated, enter proof construction *)
  if !Globals.annotate
  then (
    incr count;
    fprintf !out "<a name=\"%d\"></a>\n%!" !count;
    fprintf !out "<pre class=\"code\">\n%!");
  print_top_prompt ();
  let input = Parser.top_command Lexer.token !lexbuf in
  if not !interactive
  then (
    let pre, post = if !Globals.annotate then "<b>", "</b>" else "", "" in
    fprintf !out "%s%s%s\n%!" pre (Print.string_of_topcommand input) post);
  (match input with
  | Uterms.Theorem (name, uthm) ->
    let theorem =
      Translate.trans_formula
        !Prover.lf_sig
        !Prover.schemas
        (Prover.get_propty_lst ())
        []
        []
        []
        []
        uthm
    in
    Prover.set_sequent (Sequent.make_sequent_from_goal ~name ~form:theorem ());
    (try
       Prover.display_state ();
       proof_loop ()
     with
    | Prover.ProofCompleted ->
      print_endline "Proof Completed!";
      Prover.add_lemma name theorem
    | End_of_file ->
      print_endline "Proof Aborted.";
      Prover.reset_prover ());
    ()
  | Uterms.Schema (name, uschema) ->
    let schema = Translate.trans_schema !Prover.lf_sig uschema in
    Prover.add_schema name schema;
    ()
  | Uterms.Specification fid ->
    read_spec fid;
    ()
  | Quit -> raise End_of_file
  | Uterms.Define ((id, Some ty), udefs) ->
    let dfn =
      Translate.trans_dfn
        !Prover.lf_sig
        !Prover.schemas
        (Prover.get_propty_lst ())
        id
        ty
        udefs
    in
    Prover.add_definition dfn;
    ()
  | Uterms.Define ((_, None), _) -> bugf "Expected to defined some type");
  if !interactive then flush stdout;
  if !Globals.annotate then fprintf !out "</pre>%!";
  fprintf !out "\n%!"
;;

let rec top_loop () =
  while true do
    reset_if_interactive ();
    (try process () with
    | Sys_error s ->
      eprintf "Error:\n%!";
      eprintf "%s\n%!" s;
      interactive_or_exit ()
    | Parsing.Parse_error ->
      eprintf "Syntax error%s.\n%!" (position !lexbuf);
      Lexing.flush_input !lexbuf;
      interactive_or_exit ()
    | Translate.TypingError e ->
      eprintf "Typing error%s.\n%!" (position_range (Translate.get_error_pos e));
      eprintf "%s.\n%!" (Translate.explain_error e);
      interactive_or_exit ()
    | Failure s ->
      eprintf "Failure:%s\n%!" s;
      interactive_or_exit ());
    top_loop ()
  done
;;

let () =
  parse_args ();
  checkInput ();
  print_endline welcome_message;
  try top_loop () with
  | End_of_file ->
    if !interactive
    then interactive_or_exit ()
    else (
      fprintf !out "%s\n" exit_message;
      if !Globals.annotate then fprintf !out "</pre>\n%!";
      exit 0)
;;
