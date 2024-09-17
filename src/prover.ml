open Sequent
open Extensions
module H = Hashtbl

(* exception to indicate that a proof is completed (no more subgoals) *)
exception ProofCompleted

(** The state of the system includes:
    1. The LF signature
    2. The defined context schemas
    3. The lemmas
    4. The current goal
    5. The current (stack) of subgoals
    6. The available definitions
    7. The current settings
    8. The induction count
    **)

type prover_settings = { mutable search_depth : int }

(* 1. The currently loaded LF signature *)
let lf_sig = State.rref Signature.empty
let sub_rel = State.rref Subordination.empty

let clear_sig () =
  lf_sig := Signature.empty;
  sub_rel := Subordination.empty
;;

let set_sig s =
  lf_sig := s;
  sub_rel := Subordination.sub_relation s
;;

let has_sig () = !lf_sig = Signature.empty |> not

(* 2. The available context schemas *)
let schemas : (string, Context.ctx_schema) H.t = State.table ()

(* Raises Not_found if schema of given name is not in the schema list *)
let lookup_schema id = H.find schemas id

let add_schema id s =
  if H.mem schemas id
  then Format.eprintf "Warning:@ overriding@ existing@ schema@ named@ `%s'@." id;
  H.replace schemas id s
;;

(* 3. The available lemmas *)
let lemmas : (string, Formula.formula) H.t = State.table ()
let lookup_lemma id = H.find lemmas id

let add_lemma id f =
  if H.mem lemmas id
  then Format.eprintf "Warning:@ overriding@ existing@ lemma@ named@ `%s'@." id;
  H.replace lemmas id f
;;

let sequent =
  State.make
    ~copy:cp_sequent
    ~assign:assign_sequent
    { vars = []
    ; ctxvars = Context.CtxVarCtx.empty ()
    ; hyps = []
    ; goal = Formula.Top
    ; count = 0
    ; name = "dummy"
    ; next_subgoal_id = 1
    }
;;

let get_sequent () = sequent
let set_sequent other = assign_sequent sequent other
let copy_sequent () = cp_sequent sequent

(* 5. The current stack of subgoals. *)
type subgoal = unit -> unit

let subgoals : subgoal list ref = State.rref []

let add_subgoals (new_subgoals : subgoal list) =
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
let dfns : (string, Definition.dfn) H.t = State.table ()
let lookup_definition id = H.find dfns id |> snd
let get_propty_lst () = H.to_seq dfns |> Seq.map (fun (x, (y, _)) -> x, y) |> List.of_seq

let add_definition (id, dfn) =
  if H.mem dfns id
  then Format.eprintf "Warning:@ overriding@ existing@ definition@ named@ `%s'@." id;
  H.replace dfns id dfn
;;

(* 7. The current settings *)
(* How deep to extract types from hypotheses  *)
let copy_settings ss = { search_depth = ss.search_depth }
let set_setting_state s1 s2 = s1.search_depth <- s2.search_depth

let settings =
  State.make ~copy:copy_settings ~assign:set_setting_state { search_depth = 5 }
;;

let depth_or_default depth =
  match depth with
  | Uterms.DefaultDepth -> settings.search_depth
  | Uterms.WithDepth d -> d
;;

(* 8. Induction count *)
let ind_count = State.rref 0

let get_ind_count () =
  let _ = ind_count := 1 + !ind_count in
  !ind_count
;;

let reset_ind_count () = ind_count := 0

let change_settings sets =
  let aux setting =
    match setting with
    | Uterms.SearchDepth v -> settings.search_depth <- v
  in
  List.iter aux sets
;;

let reset_prover =
  let empty_bind_state = Term.get_bind_state () in
  let empty_seq = copy_sequent () in
  fun () ->
    set_sequent empty_seq;
    subgoals := [];
    reset_ind_count ();
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
  let snapshot = State.snapshot () in
  (*let bind_state = Term.get_bind_state () in*)
  Print.print_sequent sequent;
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
  State.reload snapshot
;;

(*Term.set_bind_state bind_state*)

let induction i = Tactics.ind sequent i (get_ind_count ())
let intros () = Tactics.intros sequent

let case_to_subgoal remove h_name case : subgoal =
  fun () ->
  sequent.vars <- case.Tactics.vars_case;
  sequent.ctxvars <- case.Tactics.ctxvars_case;
  sequent.hyps <- case.Tactics.hyps_case;
  sequent.goal <- case.Tactics.goal_case;
  sequent.count <- case.Tactics.count_case;
  sequent.name <- case.Tactics.name_case;
  sequent.next_subgoal_id <- case.Tactics.next_subgoal_id_case;
  if remove then Sequent.remove_hyp sequent h_name;
  Term.set_bind_state case.Tactics.bind_state_case
;;

(* the unification for first case is modifying the sequent. need to make a true copy where
   the vars are different or find another way to reset so we can try next unification *)
let case remove hyp =
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
            sequent.ctxvars <- Context.CtxVarCtx.copy seq.ctxvars;
            sequent.hyps <- seq.hyps;
            sequent.goal <- seq.goal;
            sequent.count <- seq.count;
            sequent.name <- sequent.name;
            sequent.next_subgoal_id <- seq.next_subgoal_id;
            Term.set_bind_state bind_state)
        ]
    | Formula.Atm _ ->
      (match Tactics.cases !lf_sig schemas sequent hyp with
       | [] -> next_subgoal ()
       | cases ->
         add_subgoals (List.map (case_to_subgoal remove hyp) cases);
         next_subgoal ())
    | _ -> ()
  with
  | Tactics.NotLlambda -> failwith "cases failed: not llambda"
  | Not_found -> failwithf "No assumption of name `%s'." hyp
;;

let exists tm =
  try Tactics.exists sequent tm with
  | Typing.TypeError (exp, got) ->
    failwithf
      "Type Error: Expected type\n%s\nbut found type\n%s"
      (Print.string_of_ty exp)
      (Print.string_of_ty got)
  | Tactics.InvalidTerm _ -> failwith "Bad term"
;;

let skip () = next_subgoal ()

let search depth () =
  let depth = depth_or_default depth in
  match sequent.goal with
  | Formula.Atm _ | Formula.Prop _ ->
    (try
       Tactics.search ~depth !lf_sig sequent;
       let msg =
         Format.asprintf
           "@[<hv1>@[Search@ failed.@]@ @[Unable@ to@ determine@ validity@ of:@]@ \
            @[<1>%a@]"
           Print.pr_typing_judgement
           sequent.goal
       in
       failwith msg
     with
     | Tactics.Success -> next_subgoal ())
  | Formula.Top -> next_subgoal ()
  | _ ->
    if List.exists (fun h -> h.formula = Formula.Bottom) sequent.hyps
    then next_subgoal ()
    else failwith "Cannot apply search to goal formula of this structure."
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
               sequent.ctxvars
               ctxtm
               (schemaid, lookup_schema schemaid)
          then id, ctxtm
          else
            raise
              (ApplyFailure
                 (Format.asprintf
                    "@[<hv1>@[Context@ expression@] @[<1>%a@] @[does@ not@ match@ \
                     schema@]@ @[%s@].@]"
                    Print.pr_ctxexpr
                    ctxtm
                    schemaid))
        with
        | Not_found -> raise (ApplyFailure ("Unknown context variable " ^ id)))
      cwiths )
;;

(* let freshen_formula_names f (vwiths, cwiths) = let support =
   Formula.formula_support_sans (Sequent.get_cvar_tys sequent.Sequent.ctxvars) f in let
   withs_used = Term.find_var_refs Term.Nominal (List.map snd vwiths) @ List.flatten
   (List.map (fun (_, ctxexpr) -> Formula.context_support_sans (Sequent.get_cvar_tys
   sequent.Sequent.ctxvars) ctxexpr) cwiths) in (* let used = ref (List.filter (fun (_,t)
   -> Term.is_var Nominal t) sequent.vars) in *) let torename = List.intersect support
   withs_used in let used = ref (List.map Term.term_to_pair (List.unique (withs_used @
   support))) in let rename = List.map (fun t -> let t', used' = Term.fresh_wrt ~ts:3
   Nominal "n" (Term.get_var_ty t) !used in used := used'; Term.get_id t, t') torename in
   List.iter (fun (_, t) -> Sequent.add_var sequent (Term.term_to_pair t)) rename;
   Formula.replace_formula_vars rename f ;; *)

let term_vars_alist tag terms = List.map Term.term_to_pair (Term.find_var_refs tag terms)

let formula_vars_alist tag ctxvars formula =
  term_vars_alist tag (Formula.collect_terms ctxvars formula)
;;

let formula_free_logic_vars ctxvars formula =
  let bound_ctxvars = Context.CtxVarCtx.empty () in
  let rec get_atomic bndrs formula =
    match formula with
    | Formula.Ctx (cbndrs, body) ->
      let _ =
        Context.CtxVarCtx.add_vars
          bound_ctxvars
          (List.map
             (fun (vid, vty) ->
               Context.ctx_var vid, (ref VarSet.empty, Context.CtxTy (vty, [])))
             cbndrs)
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
    List.flatten_map
      (formula_vars_alist Term.Logic (Context.CtxVarCtx.union bound_ctxvars ctxvars))
      atoms
  in
  List.remove_all (fun (id, _) -> List.mem id bound_vars) logic_vars
;;

(* check the given formula for logic variables. Assumes that any context variable
   appearing in the formula f is a member of the context variable context ctxvarctx.*)
let ensure_no_logic_variable ctxvarctx f =
  let logic_vars = formula_free_logic_vars (Context.CtxVarCtx.copy ctxvarctx) f in
  if logic_vars <> [] then raise (ApplyFailure "Found logic variable at toplevel.")
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
         (Format.asprintf
            "@[<hv1>@[Unable@ to@ find@ instantiation@ for@ context@ variable:@]@ \
             @[<1>%s@]@ @[in@ formula:@]@ @[%a@]@]"
            (List.hd ctx_vars)
            Print.pr_formula
            f))
;;

let find_lemma_opt name = H.find_opt lemmas name

let find_by_name name =
  match find_lemma_opt name with
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
  let res_f = Tactics.apply_with schemas ~sub_rel:!sub_rel sequent f forms withs in
  let () =
    ensure_no_uninst_ctxvariable
      (Context.CtxVarCtx.get_var_tys sequent.Sequent.ctxvars)
      res_f
  in
  let () = ensure_no_logic_variable sequent.Sequent.ctxvars res_f in
  res_f
;;

(* Generate a substitution for every nominal in [form] to new nominals away from the
   support set of the sequent. Also modifies the sequent to add the newly inserted
   variables into its support set.

   @param [form] the formula in which all nominals will be substituted for

   @return the new formula with fresh nominals *)
let freshen_nominals (form : Formula.formula) : Formula.formula =
  let nominals = Formula.get_formula_used_nominals sequent.Sequent.ctxvars form in
  let nvars = Sequent.get_nominals sequent in
  let used = ref nvars in
  let alist =
    List.map
      (fun (id, t) ->
        let t', used' =
          Term.fresh_wrt ~ts:2 Term.Nominal "n" (Term.term_to_var t).Term.ty !used
        in
        used := used';
        id, t')
      nominals
  in
  (* Add all new nominals to the sequent *)
  List.map (fun (_, dest) -> Term.term_to_pair dest) alist
  |> List.iter (Sequent.add_var sequent);
  Formula.replace_formula_vars alist form
;;

let apply name args uws =
  try
    let f =
      match find_lemma_opt name with
      | Some f -> freshen_nominals f
      | None -> find_by_name name
    in
    let forms = List.map find_by_name args in
    let res_f = apply_form f forms uws in
    Sequent.add_hyp sequent res_f;
    Sequent.normalize_hyps sequent;
    Sequent.prune_noms sequent
  with
  | Unify.UnifyFailure e -> failwith (Unify.explain_failure e)
  | ApplyFailure str -> failwith str
  | Tactics.AmbiguousSubst (ctx1, ctx2) ->
    let msg =
      Format.asprintf
        "@[<hv>@[Ambiguous@ context@ substitution.@ Found:@]@ @[<v>@[<2>%a@]@ @[ and@]@ \
         @[<2>%a@]@]@]"
        Print.pr_ctxexpr
        ctx1
        Print.pr_ctxexpr
        ctx2
    in
    failwith msg
  | Failure e -> failwith e
;;

let assert_thm depth f =
  let seq_var_ids =
    Sequent.get_nominals sequent |> List.map (fun (_, v) -> Term.term_to_var v)
  in
  let new_vars =
    Formula.collect_vars_ctx f |> List.remove_all (fun t -> List.mem t seq_var_ids)
  in
  let new_noms =
    List.fold_left
      (fun l v ->
        let n, _ = Term.fresh_wrt ~ts:3 Term.Nominal "n" v.Term.ty (l @ sequent.vars) in
        (Term.term_to_name n, n) :: l)
      []
      new_vars
  in
  let alist =
    List.combine (List.map (fun v -> v.Term.name) new_vars) (List.map snd new_noms)
  in
  let f' = Formula.replace_formula_vars alist f in
  List.iter (fun v -> Sequent.add_var sequent v) new_noms;
  let depth = depth_or_default depth in
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
      add_hyp sequent f'
  in
  add_subgoals [ subgoal ];
  sequent.goal <- f';
  match sequent.goal with
  | Formula.Atm _ | Formula.Prop _ ->
    (try Tactics.search ~depth !lf_sig sequent with
     | Tactics.Success -> next_subgoal ())
  | Formula.Top -> next_subgoal ()
  | _ ->
    if List.exists (fun h -> h.formula = Formula.Bottom) sequent.hyps then next_subgoal ()
;;

let split () =
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
  | Tactics.InvalidFormula (_, str) -> failwith str
;;

let left () =
  try
    let l = Tactics.left sequent.goal in
    sequent.goal <- l
  with
  | Tactics.InvalidFormula (_, str) -> failwith str
;;

let right () =
  try
    let r = Tactics.right sequent.goal in
    sequent.goal <- r
  with
  | Tactics.InvalidFormula (_, str) -> failwithf "Invalid formula:\n%s" str
;;

let weaken depth remove id ty =
  try
    let depth = depth_or_default depth in
    let hyp = (Sequent.get_hyp sequent id).formula in
    Tactics.weaken ~depth !lf_sig sequent hyp ty;
    failwith "Weakening failed."
  with
  | Not_found -> failwithf "No assumption of name `%s'\n." id
  | Tactics.InvalidFormula (_, str) -> failwithf "Invalid formula:\n%s" str
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
        Context.CtxVarCtx.restrict_in
          sequent.ctxvars
          (Context.get_ctx_var g)
          [ Term.term_to_var nvar ]
      in
      ());
    Sequent.add_var sequent (Term.term_to_pair nvar);
    Sequent.add_hyp
      sequent
      (Formula.atm ~ann (Context.Ctx (g, (Term.term_to_var nvar, ty))) a m)
  | Tactics.InvalidName id -> failwithf "`%s' is not a valid type constant." id
  | Tactics.InvalidTerm t ->
    Format.asprintf "Given@ expression@ `%a'@ is@ not@ a@ type." (Print.pr_term []) t
    |> failwith
;;

let permute_ctx remove hyp_name ctx_expr =
  try
    let form = (Sequent.get_hyp sequent hyp_name).formula in
    let form' = Tactics.permute_ctx form ctx_expr in
    if remove
    then Sequent.replace_hyp sequent hyp_name form'
    else Sequent.add_hyp sequent form'
  with
  | Not_found -> failwithf "No hyp of name `%s' found." hyp_name
  | Tactics.InvalidCtxPermutation str ->
    failwithf "Not a valid context permutation.\n%s" str
;;

let permute remove name perm =
  try
    let f = (Sequent.get_hyp sequent name).formula in
    let f' = Tactics.permute f perm sequent in
    if remove then Sequent.replace_hyp sequent name f' else Sequent.add_hyp sequent f'
  with
  | Tactics.PermutationFailure (OutOfResSetPermutation ns) ->
    Format.asprintf
      "@[<hv>@[Permutation@ provided@ can@ only@ contain@ nominals@ in@ the@ restricted@ \
       set.@] @[Mappings@ not@ allowed@ for:@ %s@]@]"
      (String.concat ", " ns)
    |> failwith
  | Tactics.PermutationFailure (MultiMappedPermutation ns) ->
    Format.asprintf
      "@[<hv>@[Multiple@ mappings found for:@] @[%s@]@]"
      (String.concat ", " ns)
    |> failwith
  | Tactics.PermutationFailure (IncompletePermutation ns) ->
    Format.asprintf
      "@[<hv>@[Permutation@ provided@ is@ not@ complete.@] @[Mappings@ required@ for:@] \
       @[%s@]@]"
      (String.concat ", " ns)
    |> failwith
  | Not_found -> failwithf "No hyp of name `%s' found." name
;;

let strengthen remove name =
  try
    match (Sequent.get_hyp sequent name).formula with
    | Formula.Atm (Context.Ctx _, _, _, _) as f ->
      (match Tactics.strengthen sequent.ctxvars f with
       | Some f_op ->
         Sequent.add_hyp sequent f_op;
         if remove then Sequent.remove_hyp sequent name
       | None -> ())
    | Formula.Atm _ ->
      failwith "Strengthening can only be performed on explicit context items."
    | _ -> failwith "Strengthening can only be performed on atomic formulas."
  with
  | Not_found -> failwithf "No hyp of name `%s' found." name
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
      else raise (InstError (Format.sprintf "`%s' is not an instantiable name." id))
  in
  let typed_withs = List.map check_withs withs in
  let depth = depth_or_default depth in
  Tactics.inst ~depth !lf_sig sequent form typed_withs
;;

let inst depth remove name withs =
  try
    let _ =
      if List.length withs > 1 || List.length withs <= 0
      then raise (InstError "Exactly one instantiation must be provided.")
    in
    let form' = inst_aux depth name withs in
    if remove then Sequent.remove_hyp sequent name;
    Sequent.add_hyp sequent form'
  with
  | InstError str -> failwith str
  | Tactics.InstTypeError f ->
    failwithf "Unable to derive formula:\n%s" (Print.string_of_formula f)
;;

let prune name =
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
    | Formula.Atm (_, m, _, _) when check_term (Term.norm m) ->
      Tactics.prune !sub_rel sequent f
    | _ ->
      failwith
        "Pruning formulas must be of the form {G |- X n1 ... nm : A} with n1,...,nm \
         distinct."
  with
  | Not_found -> failwithf "No hyp of name `%s' found." name
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
      | _ -> raise (ApplyFailure "Only proposition formulas can be unfolded.")
    in
    (* for each clause of the definition, construct the formula and try applying *)
    let f' =
      let rec try_each = function
        | (_, tyctx, f1, f2) :: defs' ->
          let pristine = State.snapshot () in
          (try
             let f_def = Formula.forall tyctx (Formula.imp f1 f2) in
             apply_form f_def [ f ] uwiths
           with
           | _ ->
             State.reload pristine;
             try_each defs')
        | [] -> raise (ApplyFailure "No clauses of definition match.")
      in
      try_each defs
    in
    if Option.is_some hypop
    then Sequent.replace_hyp sequent (Option.get hypop) f'
    else sequent.goal <- f'
  with
  | ApplyFailure str -> failwith str
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
          let pristine = State.snapshot () in
          (try
             let f_def = Formula.forall tyctx (Formula.imp f2 f1) in
             apply_form f_def [ f ] uwiths
           with
           | _ ->
             State.reload pristine;
             try_each defs')
        | [] -> raise (ApplyFailure "No clauses of definition match.")
      in
      try_each defs
    in
    if Option.is_some hypnameop
    then Sequent.replace_hyp sequent (Option.get hypnameop) f'
    else sequent.goal <- f'
  with
  | ApplyFailure str -> failwith str
;;
