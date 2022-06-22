open Sequent
open Extensions

(* exception to indicate that a proof is completed (no more subgoals) *)
exception ProofCompleted

(** The state of the system includes:
    1. The LF signature
    2. The defined context schemas
    3. The lemmas
    4. The current goal
    5. The current (stack) of subgoals
    6. The available definitions
**)

(* 1. The currently loaded LF signature *)
let lf_sig = ref Signature.empty
let clear_sig () = lf_sig := Signature.empty
let set_sig s = lf_sig := s

(* 2. The available context schemas *)
let schemas : (string * Context.ctx_schema) list ref = ref []
let add_schema id s = schemas := (id, s) :: !schemas
let clear_schemas () = schemas := []

(* Raises Not_found if schema of given name is not in the schema list *)
let lookup_schema id = List.assoc id !schemas

(* How deep to extract types from hypotheses *)
let search_depth = ref 5

let depth_or_default depth =
  match depth with
  | Uterms.DefaultDepth -> !search_depth
  | Uterms.WithDepth d -> d
;;

let set_setting s =
  match s with
  | Uterms.Depth v -> search_depth := v
;;

(* 3. The available lemmas *)
let lemmas : (string * Formula.formula) list ref = ref []
let add_lemma id f = lemmas := (id, f) :: !lemmas
let clear_lemmas () = lemmas := []
let lookup_lemma id = List.assoc id !lemmas

(* 4. The current goal. *)
let sequent =
  { vars = []
  ; ctxvars = []
  ; hyps = []
  ; goal = Formula.Top
  ; count = 0
  ; name = "dummy"
  ; next_subgoal_id = 1
  }
;;

let copy_sequent () = cp_sequent sequent
let set_sequent other = assign_sequent sequent other
let get_sequent () = sequent

(* 5. The current stack of subgoals. *)
let subgoals : (unit -> unit) list ref = ref []

let add_subgoals (new_subgoals : (unit -> unit) list) =
  let extend_name sequent i =
    if sequent.name = ""
    then sequent.name <- string_of_int i
    else sequent.name <- sequent.name ^ "." ^ string_of_int i
  in
  let rec annotate i gs =
    match gs with
    | [] -> []
    | g :: rest ->
      (fun () ->
        g ();
        extend_name sequent i;
        sequent.next_subgoal_id <- 1)
      :: annotate (i + 1) rest
  in
  let n = List.length new_subgoals in
  let annotated_subgoals =
    if n > 1 then annotate sequent.next_subgoal_id new_subgoals else new_subgoals
  in
  subgoals := annotated_subgoals @ !subgoals
;;

(* 6. The available definitions *)
let dfns : Definition.dfn list ref = ref []
let add_definition dfn = dfns := dfn :: !dfns
let clear_definitions () = dfns := []
let lookup_definition id = snd (List.assoc id !dfns)
let get_propty_lst () = List.map (fun (x, (y, _)) -> x, y) !dfns
let undo_stack = ref []

let state_snapshot () =
  ( copy_sequent ()
  , !subgoals
  , Term.get_bind_state ()
  , Term.get_varcount ()
  , Context.get_varcount () )
;;

let state_reset (seq, sgs, tbs, tvc, cvc) =
  set_sequent seq;
  subgoals := sgs;
  Term.set_bind_state tbs;
  Term.set_varcount tvc;
  Context.set_varcount cvc
;;

let save_undo_state () = undo_stack := state_snapshot () :: !undo_stack

let reset_prover =
  let empty_bind_state = Term.get_bind_state () in
  let empty_seq = copy_sequent () in
  fun () ->
    set_sequent empty_seq;
    undo_stack := [];
    subgoals := [];
    Tactics.reset_ind_count ();
    Term.set_bind_state empty_bind_state;
    Term.reset_varcount ();
    Context.reset_varcount ()
;;

let next_subgoal () =
  match !subgoals with
  | [] ->
    reset_prover ();
    raise ProofCompleted
  | set_subgoal :: rest ->
    set_subgoal ();
    subgoals := rest;
    normalize_hyps sequent;
    ()
;;

let display_state () =
  print_endline "";
  Print.print_sequent sequent;
  let snapshot, undo_state = state_snapshot (), !undo_stack in
  List.iter
    (fun subgoal ->
      subgoal ();
      Format.printf
        "@[<1>Subgoal %s%sis:@\n%a@]@\n@\n%!"
        sequent.name
        (if sequent.name = "" then "" else " ")
        Print.pr_formula
        sequent.goal)
    !subgoals;
  state_reset snapshot;
  undo_stack := undo_state
;;

(* print_endline ("Number Subgoals: "^(string_of_int (List.length (!subgoals)))^"\n\n") *)

(* not fully implemented undo function yet *)
let undo () =
  match !undo_stack with
  | snapshot :: rest ->
    state_reset snapshot;
    undo_stack := rest
  | [] -> prerr_endline "Nothing left to undo"
;;

let induction i =
  save_undo_state ();
  try Tactics.ind sequent i with
  | e ->
    undo ();
    raise e
;;

let intros () =
  save_undo_state ();
  try Tactics.intros sequent with
  | e ->
    undo ();
    raise e
;;

let case_to_subgoal remove h_name case =
  let saved_sequent = copy_sequent () in
  fun () ->
    (* set_sequent saved_sequent; *)
    saved_sequent.vars <- case.Tactics.vars_case;
    saved_sequent.ctxvars <- case.Tactics.ctxvars_case;
    saved_sequent.hyps <- case.Tactics.hyps_case;
    saved_sequent.goal <- case.Tactics.goal_case;
    saved_sequent.count <- case.Tactics.count_case;
    saved_sequent.name <- case.Tactics.name_case;
    saved_sequent.next_subgoal_id <- case.Tactics.next_subgoal_id_case;
    if remove then Sequent.remove_hyp saved_sequent h_name;
    Term.set_bind_state case.Tactics.bind_state_case;
    set_sequent saved_sequent
;;

(* the unification for first case is modifying the sequent.
  need to make a true copy where the vars are different or
  find another way to reset so we can try next unification *)
let case remove hyp =
  save_undo_state ();
  try
    match (Sequent.get_hyp sequent hyp).formula with
    | Formula.Bottom -> next_subgoal ()
    | Formula.And (g1, g2) ->
      if remove then Sequent.remove_hyp sequent hyp;
      Sequent.add_hyp sequent g1;
      Sequent.add_hyp sequent g2
    | Formula.Or (g1, g2) ->
      let seq = copy_sequent () in
      let bind_state = Term.get_bind_state () in
      if remove
      then (
        Sequent.replace_hyp sequent hyp g1;
        Sequent.replace_hyp seq hyp g2)
      else (
        Sequent.add_hyp sequent g1;
        Sequent.add_hyp seq g2);
      add_subgoals
        [ (fun () ->
            sequent.vars <- seq.vars;
            sequent.ctxvars <- seq.ctxvars;
            sequent.hyps <- seq.hyps;
            sequent.goal <- seq.goal;
            sequent.count <- seq.count;
            sequent.name <- sequent.name;
            sequent.next_subgoal_id <- seq.next_subgoal_id;
            Term.set_bind_state bind_state)
        ]
    | Formula.Atm _ ->
      (match Tactics.cases !lf_sig !schemas sequent hyp with
      | [] -> next_subgoal ()
      | cases ->
        add_subgoals (List.map (case_to_subgoal remove hyp) cases);
        next_subgoal ())
    | _ -> ()
  with
  | Tactics.NotLlambda ->
    prerr_endline "cases failed: not llambda";
    undo ()
  | Not_found ->
    prerr_endline ("No assumption of name `" ^ hyp ^ "'.");
    undo ()
;;

let exists tm =
  save_undo_state ();
  try Tactics.exists sequent tm with
  | Typing.TypeError (exp, got) ->
    prerr_endline
      ("Type Error: Expected type\n"
      ^ Print.string_of_ty exp
      ^ "\nbut found type\n"
      ^ Print.string_of_ty got);
    undo ()
  | Tactics.InvalidTerm _ ->
    prerr_endline "Bad term";
    undo ()
;;

let skip () =
  save_undo_state ();
  next_subgoal ()
;;

let search depth () =
  let _ = save_undo_state () in
  let depth = depth_or_default depth in
  match sequent.goal with
  | Formula.Atm _ | Formula.Prop _ ->
    (try
       Tactics.search ~depth !lf_sig sequent;
       undo ();
       prerr_endline "Search failed."
     with
    | Tactics.Success -> next_subgoal ())
  | Formula.Top -> next_subgoal ()
  | _ ->
    if List.exists (fun h -> h.formula = Formula.Bottom) sequent.hyps
    then next_subgoal ()
    else (
      prerr_endline "Cannot apply search to goal formula of this structure.";
      undo ())
;;

let toplevel_bindings form =
  let rec aux = function
    | Formula.All (tids, t) ->
      let alls, ctxs = aux t in
      tids @ alls, ctxs
    | Formula.Ctx (cids, t) ->
      let alls, ctxs = aux t in
      alls, cids @ ctxs
    | _ -> [], []
  in
  aux form
;;

exception ApplyFailure of string

let type_apply_withs form (vwiths, cwiths) =
  let all_bindings, ctx_bindings = toplevel_bindings form in
  let nvars = List.filter (fun (_, t) -> Term.is_var Term.Nominal t) sequent.vars in
  let evars = List.filter (fun (_, t) -> Term.is_var Term.Eigen t) sequent.vars in
  let evar_ctx = List.map (fun (_, t) -> Term.get_id t, ref (Some t)) evars in
  let nvar_ctx = List.map (fun (_, t) -> Term.get_id t, ref (Some t)) nvars in
  ( List.map
      (fun (id, t) ->
        try
          let ty = List.assoc id all_bindings in
          let tm, new_nvarctx =
            Translate.trans_term !lf_sig evar_ctx [] nvar_ctx [] (Some ty) t
          in
          (* we can assume that all the nvars in the list have been typed by this point *)
          List.iter
            (Sequent.add_var sequent)
            (List.map (fun (id, r) -> id, Option.get !r) new_nvarctx);
          id, tm
        with
        | Not_found -> raise (ApplyFailure ("Unknown variable " ^ id)))
      vwiths
  , List.map
      (fun (id, cexpr) ->
        try
          let schemaid = List.assoc id ctx_bindings in
          let ctxtm, new_nvarctx =
            Translate.trans_ctx !lf_sig evar_ctx [] sequent.ctxvars nvar_ctx cexpr
          in
          List.iter
            (Sequent.add_var sequent)
            (List.map (fun (id, r) -> id, Option.get !r) new_nvarctx);
          if Typing.of_schema
               nvars
               (Sequent.get_cvar_tys sequent.ctxvars)
               ctxtm
               (schemaid, lookup_schema schemaid)
          then id, ctxtm
          else
            raise
              (ApplyFailure
                 ("Context expression "
                 ^ Print.string_of_ctxexpr ctxtm
                 ^ " does not match schema "
                 ^ schemaid
                 ^ "."))
        with
        | Not_found -> raise (ApplyFailure ("Unknown context variable " ^ id)))
      cwiths )
;;

(*
let freshen_formula_names f (vwiths, cwiths) =
  let support =
    Formula.formula_support_sans (Sequent.get_cvar_tys sequent.Sequent.ctxvars) f
  in
  let withs_used =
    Term.find_var_refs Term.Nominal (List.map snd vwiths)
    @ List.flatten
        (List.map
           (fun (_, ctxexpr) ->
             Formula.context_support_sans
               (Sequent.get_cvar_tys sequent.Sequent.ctxvars)
               ctxexpr)
           cwiths)
  in
  (* let used = ref (List.filter (fun (_,t) -> Term.is_var Nominal t) sequent.vars) in *)
  let torename = List.intersect support withs_used in
  let used = ref (List.map Term.term_to_pair (List.unique (withs_used @ support))) in
  let rename =
    List.map
      (fun t ->
        let t', used' = Term.fresh_wrt ~ts:3 Nominal "n" (Term.get_var_ty t) !used in
        used := used';
        Term.get_id t, t')
      torename
  in
  List.iter (fun (_, t) -> Sequent.add_var sequent (Term.term_to_pair t)) rename;
  Formula.replace_formula_vars rename f
;;
*)

let term_vars_alist tag terms = List.map Term.term_to_pair (Term.find_var_refs tag terms)

let formula_vars_alist tag ctxvars formula =
  term_vars_alist tag (Formula.collect_terms ctxvars formula)
;;

let formula_free_logic_vars ctxvars formula =
  let bound_ctxvars = ref [] in
  let rec get_atomic bndrs formula =
    match formula with
    | Formula.Ctx (cbndrs, body) ->
      let _ =
        bound_ctxvars
          := List.map
               (fun (vid, vty) -> Context.ctx_var vid, Context.CtxTy (vty, []))
               cbndrs
             @ !bound_ctxvars
      in
      get_atomic bndrs body
    | Formula.All (vs, body) | Formula.Exists (vs, body) ->
      let bndrs' = bndrs @ List.map fst vs in
      get_atomic bndrs' body
    | Formula.Imp (f1, f2) | Formula.And (f1, f2) | Formula.Or (f1, f2) ->
      let bndrs1, atms1 = get_atomic bndrs f1 in
      let bndrs2, atms2 = get_atomic bndrs f2 in
      bndrs1 @ bndrs2, atms1 @ atms2
    | _ -> bndrs, [ formula ]
  in
  let bound_vars, atoms = get_atomic [] formula in
  let logic_vars =
    List.flatten
      (List.map (formula_vars_alist Term.Logic (!bound_ctxvars @ ctxvars)) atoms)
  in
  List.filter (fun (id, _) -> not (List.mem id bound_vars)) logic_vars
;;

(* check the given formula for logic variables. 
   Assumes that any context variable appearing in the formula f
   is a member of the context variable context ctxvarctx.*)
let ensure_no_logic_variable ctxvarctx f =
  let logic_vars = formula_free_logic_vars ctxvarctx f in
  if logic_vars <> [] then raise (ApplyFailure "Found logic varaible at toplevel.")
;;

(* ensure that no dummy context variables remain in the formula *)
let ensure_no_uninst_ctxvariable ctxvarctx f =
  let ctx_vars =
    List.filter
      (fun ctxvar -> not (List.mem ctxvar (List.map fst ctxvarctx)))
      (Formula.get_formula_used_ctxvars f)
  in
  if ctx_vars <> []
  then
    raise
      (ApplyFailure
         ("Unable to find instantiation for context variable: "
         ^ List.hd ctx_vars
         ^ ".\nIn formula: "
         ^ Print.string_of_formula f))
;;

let find_by_name name =
  match List.assoc_opt name !lemmas with
  | Some form -> form
  | None ->
    (try (Sequent.get_hyp sequent name).Sequent.formula with
    | Not_found ->
      raise (ApplyFailure ("Formula `" ^ name ^ "' not found in lemmas or assumption.")))
;;

let apply_form f forms uws =
  let vwiths, cwiths = List.partition Uterms.is_vws uws in
  let withs =
    type_apply_withs
      f
      (List.map Uterms.unwrap_vws vwiths, List.map Uterms.unwrap_cws cwiths)
  in
  (* let f' = freshen_formula_names (Formula.copy_formula f) withs in *)
  (* let res_f = Tactics.apply_with !schemas sequent f' forms withs in *)
  let res_f = Tactics.apply_with !schemas sequent f forms withs in
  let () =
    ensure_no_uninst_ctxvariable (Sequent.get_cvar_tys sequent.Sequent.ctxvars) res_f
  in
  let () =
    ensure_no_logic_variable (Sequent.get_cvar_tys sequent.Sequent.ctxvars) res_f
  in
  res_f
;;

let apply name args uws =
  save_undo_state ();
  try
    let f = find_by_name name in
    let forms = List.map find_by_name args in
    let res_f = apply_form f forms uws in
    Sequent.add_hyp sequent res_f;
    Sequent.normalize_hyps sequent
  with
  | Unify.UnifyFailure e ->
    prerr_endline (Unify.explain_failure e);
    undo ()
  | ApplyFailure str ->
    prerr_endline str;
    undo ()
  | Failure e ->
    prerr_endline e;
    undo ()
;;

let assert_thm f =
  save_undo_state ();
  let subgoal =
    let saved_sequent = copy_sequent () in
    let bind_state = Term.get_bind_state () in
    fun () ->
      sequent.vars <- saved_sequent.vars;
      sequent.ctxvars <- saved_sequent.ctxvars;
      sequent.hyps <- saved_sequent.hyps;
      sequent.goal <- saved_sequent.goal;
      sequent.count <- saved_sequent.count;
      sequent.name <- saved_sequent.name;
      sequent.next_subgoal_id <- saved_sequent.next_subgoal_id;
      Term.set_bind_state bind_state;
      add_hyp sequent f
  in
  add_subgoals [ subgoal ];
  sequent.goal <- f
;;

let split () =
  save_undo_state ();
  try
    let g1, g2 = Tactics.split sequent.goal in
    let seq = copy_sequent () in
    let bind_state = Term.get_bind_state () in
    sequent.goal <- g1;
    add_subgoals
      [ (fun () ->
          sequent.vars <- seq.vars;
          sequent.ctxvars <- seq.ctxvars;
          sequent.hyps <- seq.hyps;
          sequent.goal <- g2;
          sequent.count <- seq.count;
          sequent.name <- sequent.name;
          sequent.next_subgoal_id <- seq.next_subgoal_id;
          Term.set_bind_state bind_state)
      ]
  with
  | Tactics.InvalidFormula (_, str) ->
    prerr_endline str;
    undo ()
;;

let left () =
  save_undo_state ();
  try
    let l = Tactics.left sequent.goal in
    sequent.goal <- l
  with
  | Tactics.InvalidFormula (_, str) ->
    prerr_endline str;
    undo ()
;;

let right () =
  save_undo_state ();
  try
    let r = Tactics.right sequent.goal in
    sequent.goal <- r
  with
  | Tactics.InvalidFormula (_, str) ->
    prerr_endline str;
    undo ()
;;

let weaken depth remove id ty =
  save_undo_state ();
  try
    let depth = depth_or_default depth in
    let hyp = (Sequent.get_hyp sequent id).formula in
    Tactics.weaken ~depth !lf_sig sequent hyp ty;
    prerr_endline "weakening failed.";
    undo ()
  with
  | Not_found ->
    prerr_endline ("No assumption of name `" ^ id ^ "'.");
    undo ()
  | Tactics.InvalidFormula (_, str) ->
    prerr_endline str;
    undo ()
  | Tactics.Success ->
    let g, a, m, ann =
      let f = (Sequent.get_hyp sequent id).formula in
      match f with
      | Formula.Atm (g, a, m, ann) -> g, a, m, ann
      | _ -> bugf "Non-atomic formula not expected"
    in
    let _ = if remove then Sequent.remove_hyp sequent id in
    let nvar, _ =
      Term.fresh_wrt
        ~ts:3
        Term.Nominal
        "n"
        (Term.erase ty)
        (List.filter (fun (_, t) -> Term.is_var Term.Nominal t) sequent.vars)
    in
    if Context.has_var g
    then (
      let _ =
        restrict_in
          (ctxvar_lookup sequent.ctxvars (Context.get_ctx_var g))
          [ Term.get_id nvar ]
      in
      ());
    Sequent.add_var sequent (Term.term_to_pair nvar);
    Sequent.add_hyp
      sequent
      (Formula.atm ~ann (Context.Ctx (g, (Term.term_to_var nvar, ty))) a m)
  | Tactics.InvalidName id ->
    prerr_endline ("`" ^ id ^ "' is not a valid type constant.");
    undo ()
  | Tactics.InvalidTerm t ->
    prerr_endline "Given expression is not a type.";
    undo ();
    raise (Tactics.InvalidTerm t)
;;

let permute_ctx remove hyp_name ctx_expr =
  save_undo_state ();
  try
    let form = (Sequent.get_hyp sequent hyp_name).formula in
    let form' = Tactics.permute_ctx form ctx_expr in
    if remove
    then Sequent.replace_hyp sequent hyp_name form'
    else Sequent.add_hyp sequent form'
  with
  | Not_found ->
    prerr_endline ("No hyp of name `" ^ hyp_name ^ "' found.");
    undo ()
  | Tactics.InvalidCtxPermutation str ->
    prerr_endline ("Error: Not a valid context permutation.\n" ^ str);
    undo ()
;;

let strengthen remove name =
  save_undo_state ();
  try
    match (Sequent.get_hyp sequent name).formula with
    | Formula.Atm (Context.Ctx _, _, _, _) as f ->
      let f_op = Tactics.strengthen sequent.ctxvars f in
      if Option.is_some f_op
      then (
        Sequent.add_hyp sequent (Option.get f_op);
        if remove then Sequent.remove_hyp sequent name)
      else undo ()
    | Formula.Atm _ ->
      prerr_endline "Strengthening can only be performed on explicit context items.";
      undo ()
    | _ ->
      prerr_endline "Strengthening can only be performed on atomic formulas.";
      undo ()
  with
  | Not_found ->
    prerr_endline ("No hyp of name `" ^ name ^ "' found.");
    undo ()
;;

exception InstError of string

let inst_aux depth name withs =
  let nvars = List.filter (fun (_, t) -> Term.is_var Term.Nominal t) sequent.vars in
  let evars = List.filter (fun (_, t) -> Term.is_var Term.Eigen t) sequent.vars in
  let evar_ctx = List.map (fun (_, t) -> Term.get_id t, ref (Some t)) evars in
  let nvar_ctx = List.map (fun (_, t) -> Term.get_id t, ref (Some t)) nvars in
  let g, form =
    try
      let f = (Sequent.get_hyp sequent name).formula in
      match f with
      | Formula.Atm (g, _, _, _) -> g, f
      | _ -> raise (InstError "Invalid formula for instantiation")
    with
    | Not_found -> raise (InstError ("No hyp of name `" ^ name ^ "' found."))
  in
  let instantiable = List.map (fun (x, _) -> x.Term.name, x) (Context.get_explicit g) in
  let check_withs = function
    | Uterms.Cws _ -> raise (InstError "Only nominal constants can be instantiated.")
    | Uterms.Vws (id, utm) ->
      if List.mem_assoc id instantiable
      then (
        let tm, _ =
          Translate.trans_term
            !lf_sig
            evar_ctx
            []
            nvar_ctx
            []
            (Some (List.assoc id instantiable).Term.ty)
            utm
        in
        id, tm)
      else raise (InstError ("`" ^ id ^ "' is not an instantiable name."))
  in
  let typed_withs = List.map check_withs withs in
  let depth = depth_or_default depth in
  Tactics.inst ~depth !lf_sig sequent form typed_withs
;;

let inst depth remove name withs =
  save_undo_state ();
  try
    let _ =
      if List.length withs > 1 || List.length withs <= 0
      then raise (InstError "Exactly one instantiation must be provided.")
    in
    let form' = inst_aux depth name withs in
    if remove then Sequent.remove_hyp sequent name;
    Sequent.add_hyp sequent form'
  with
  | InstError str ->
    prerr_endline ("Error: " ^ str);
    undo ()
  | Tactics.InstTypeError f ->
    prerr_endline ("Error: Unable to derive formula:\n    " ^ Print.string_of_formula f);
    undo ()
;;

let prune name =
  save_undo_state ();
  let check_term = function
    | Term.App (head, args) ->
      let norm_args = List.map Term.eta_normalize args in
      Term.is_var Term.Eigen head
      && List.is_unique norm_args
      && List.for_all (Term.is_var Term.Nominal) norm_args
    | _ -> false
  in
  try
    let f = (Sequent.get_hyp sequent name).formula in
    match f with
    | Formula.Atm (_, m, _, _) when check_term (Term.norm m) -> Tactics.prune sequent f
    | _ ->
      prerr_endline
        "Pruning formulas must be of the form {G |- X n1 ... nm : A} with n1,...,nm \
         distinct.";
      undo ()
  with
  | Not_found ->
    prerr_endline ("No hyp of name `" ^ name ^ "' found.");
    undo ()
;;

(* to fill in *)
let unfold hypop uwiths =
  try
    let f =
      if Option.is_some hypop then find_by_name (Option.get hypop) else sequent.goal
    in
    let defs =
      match f with
      | Formula.Prop (p, _) -> lookup_definition p
      | _ ->
        save_undo_state ();
        raise (ApplyFailure "Only proposition formulas can be unfolded.")
    in
    (* for each clause of the definition, construct the formula and try applying *)
    let f' =
      let rec try_each = function
        | (_, tyctx, f1, f2) :: defs' ->
          (try
             save_undo_state ();
             let f_def = Formula.forall tyctx (Formula.imp f1 f2) in
             apply_form f_def [ f ] uwiths
           with
          | _ ->
            undo ();
            try_each defs')
        | [] -> raise (ApplyFailure "No clauses of definition match.")
      in
      try_each defs
    in
    if Option.is_some hypop
    then Sequent.replace_hyp sequent (Option.get hypop) f'
    else sequent.goal <- f'
  with
  | ApplyFailure str ->
    prerr_endline str;
    undo ()
;;

let applydfn defname hypnameop uwiths =
  try
    let f =
      if Option.is_some hypnameop
      then find_by_name (Option.get hypnameop)
      else sequent.goal
    in
    let defs = lookup_definition defname in
    (* for each clause of the definition, construct the formula and try applying *)
    let f' =
      let rec try_each = function
        | (_, tyctx, f1, f2) :: defs' ->
          (try
             save_undo_state ();
             let f_def = Formula.forall tyctx (Formula.imp f2 f1) in
             apply_form f_def [ f ] uwiths
           with
          | _ ->
            undo ();
            try_each defs')
        | [] -> raise (ApplyFailure "No clauses of definition match.")
      in
      try_each defs
    in
    if Option.is_some hypnameop
    then Sequent.replace_hyp sequent (Option.get hypnameop) f'
    else sequent.goal <- f'
  with
  | ApplyFailure str ->
    prerr_endline str;
    undo ()
;;
