open Term
open Sequent
open Extensions

(* When an identified formula is of the wrong form.
 * Formula is the invalid formula and string describes what is
 * improper about its form. *)
exception InvalidFormula of Formula.formula * string
exception InvalidTerm of term

(* When a given name is invalid i.e. does not refer to a hypothesis in 
 * the current sequent.
 * string is the invalid name. *)
exception InvalidName of string
exception NotLlambda

(* Used to indicate that a goal is solved by case analysis 
 * constructing no subcases. *)
exception NoCases

(* Indicates a sucess in search *)
exception Success

type case =
  { vars_case : (Term.id * Term.term) list
  ; ctxvars_case : Sequent.cvar_entry list
  ; hyps_case : Sequent.hyp list
  ; goal_case : Formula.formula
  ; count_case : int
  ; name_case : string
  ; next_subgoal_id_case : int
  ; bind_state_case : Term.bind_state
  }

let make_case seq =
  { vars_case = seq.vars
  ; ctxvars_case = seq.ctxvars
  ; hyps_case = seq.hyps
  ; goal_case = seq.goal
  ; count_case = seq.count
  ; name_case = seq.name
  ; next_subgoal_id_case = seq.next_subgoal_id
  ; bind_state_case = Term.get_bind_state ()
  }
;;

let fresh_nameless_alist ~support ~tag ~ts tids =
  let ntys = List.map (tc []) support in
  List.map
    (fun (n, ty) -> n, app (eta_expand (fresh ~tag ~ts (Type.tyarrow ntys ty))) support)
    tids
;;

(* replace the given variables in a term by new eigenvariables
   which have been raised over the given support. *)
(*
let freshen_term ~used ?(support = []) (tids : (id * Type.ty) list) t =
  let alist, vars = Formula.fresh_raised_alist ~tag:Eigen ~ts:1 ~used ~support tids in
  List.map term_to_pair vars, replace_term_vars alist t
;;
*)

(* given a type Pi([(x1,A1);...;(xm,Am)],B)
   introduces new eigenvariables X1,...,Xm, raised over the given support,
   and returns the raised variable terms along with the list of types
   [A1; A2[X1 supp/x1];...;Am[X1 supp/x1,...,Xm-1 supp/xm-1];B[X1 supp/x1,...,Xm supp/xm]].

   For use in generating cases based on a given LF type. *)
let freshen_type ~used ?(support = []) = function
  | Pi (vtys, base) ->
    let vars, lftys = List.split vtys in
    let alist, _ =
      Formula.fresh_raised_alist
        ~tag:Eigen
        ~ts:1
        ~used
        ~support
        (List.map (fun v -> v.Term.name, v.Term.ty) vars)
    in
    let new_lftys =
      List.mapi (fun i typ -> replace_term_vars (List.take i alist) typ) lftys
    in
    let base' = replace_term_vars alist base in
    List.map snd alist, new_lftys, base'
  | t -> [], [], t
;;

(* freshens a block schema using new raised eigenvariables for the schema
   variables. Does not choose new names for entry items. 

   Returns the new block's entry list.*)
(*
let freshen_block ~used ?(support = []) (Context.B (schema_vars, entries)) =
  let alist, _ = Formula.fresh_raised_alist ~tag:Eigen ~used ~ts:1 ~support schema_vars in
  List.map (fun (x, y) -> x, replace_term_vars alist y) entries
;;
*)

(* replaces the given bound vars in a formula by new logic variables.*)
let freshen_nameless_bindings ~support ~ts bindings form =
  let alist = fresh_nameless_alist ~support ~tag:Logic ~ts bindings in
  Formula.replace_formula_vars alist form
;;

(* replace the given context variables in a formula with new variables. *)
let freshen_ctx_bindings ctx_vars bindings form =
  let used = ref ctx_vars in
  let aux binding =
    let name, used' = Context.fresh_wrt (fst binding) !used in
    used := used';
    name, Context.CtxTy (snd binding, [])
  in
  let new_vars = List.map aux bindings in
  let new_form =
    Formula.replace_ctx_vars
      (List.map2 (fun (bn, _) (nn, _) -> bn, Context.Var nn) bindings new_vars)
      form
  in
  new_vars, new_form
;;

(* given a context variable context, the new context variables
   (the ones which may get substitutions) and two context
   expressions, determines if g2 is an instance of g1.
   Returns the context variable substitution that
   matches the context expressions if it is an instance
   and None otherwise. *)
let context_instance schemas nvars ctxvar_ctx bound_ctxvars g1 g2 =
  (* print_endline ("Checking context\n"^(Print.string_of_ctxexpr g2)^"\nis an instance of context\n"^(Print.string_of_ctxexpr g1)); *)
  let rec aux g1 g2 =
    match g1, g2 with
    | Context.Nil, Context.Nil -> Some []
    | Context.Var v1, Context.Var v2 when v1 = v2 -> Some []
    | Context.Var v, g2 ->
      let ctxty = List.assoc_opt v (ctxvar_ctx @ bound_ctxvars) in
      if Option.is_some ctxty
      then (
        let s =
          let ctxty' = Option.get ctxty in
          match ctxty' with
          | Context.CtxTy (s, []) -> s
          | _ -> bugf "Expected a context type"
        in
        let schema = List.assoc s schemas in
        if Typing.of_schema nvars (ctxvar_ctx @ bound_ctxvars) g2 (s, schema)
        then Some [ v, g2 ]
        else None)
      else None
    | Context.Ctx (g1', (n1, ty1)), Context.Ctx (g2', (n2, ty2)) ->
      if n1 = n2
      then if Unify.try_right_unify ~used:nvars ty1 ty2 then aux g1' g2' else None
      else None
    | _, _ -> None
  in
  aux g1 g2
;;

(* Given a context variable context, determines
   if the formula f2 is an instance of the formula
   f1.
   (i.e. we can instantiate eigenvariables in f1
    s.t. it is equal to f2)
   Returns an option which contains the context variable
   substitution that makes the formulas equal if it is 
   an instance and None otherwise.
*)
let formula_instance schemas nvars ctxvar_ctx bound_ctxvars f1 f2 =
  let rec inst f1 f2 =
    match Formula.norm f1, Formula.norm f2 with
    | Formula.Top, Formula.Top | Formula.Bottom, Formula.Bottom -> Some []
    | Formula.Imp (f1l, f1r), Formula.Imp (f2l, f2r)
    | Formula.Or (f1l, f1r), Formula.Or (f2l, f2r)
    | Formula.And (f1l, f1r), Formula.And (f2l, f2r) ->
      (match inst f1l f2l with
      | Some subst -> inst (Formula.replace_ctx_vars subst f1r) f2r
      | None -> None)
    | Formula.Ctx (bndrs1, f1'), Formula.Ctx (bndrs2, f2') ->
      if List.length bndrs1 != List.length bndrs2
      then None
      else if List.fold_left2 (fun b (_, s1) (_, s2) -> b && s1 = s2) true bndrs1 bndrs2
      then (
        let subst =
          List.map2 (fun (id1, _) (id2, _) -> id1, Context.Var id2) bndrs1 bndrs2
        in
        let f = Formula.replace_ctx_vars subst f1' in
        match inst f f2' with
        | Some s -> Some (subst @ s)
        | None -> None)
      else None
    | Formula.All (vs1, f1'), Formula.All (vs2, f2')
    | Formula.Exists (vs1, f1'), Formula.Exists (vs2, f2') ->
      if List.length vs1 != List.length vs2
      then None
      else if List.fold_left2 (fun b idty1 idty2 -> b && idty1 = idty2) true vs1 vs2
      then (
        let f =
          Formula.replace_formula_vars
            (List.map (fun (n2, ty2) -> n2, var Eigen n2 0 ty2) vs2)
            f2'
        in
        inst f1' f)
      else None
    | Formula.Atm (g1, m1, a1, _), Formula.Atm (g2, m2, a2, _) ->
      if Unify.try_right_unify ~used:nvars m1 m2
         && Unify.try_right_unify ~used:nvars a1 a2
      then context_instance schemas nvars ctxvar_ctx bound_ctxvars g1 g2
      else None
    | Formula.Prop (p1, argtms1), Formula.Prop (p2, argtms2) ->
      if p1 = p2 && List.for_all2 (Unify.try_right_unify ~used:nvars) argtms1 argtms2
      then Some []
      else None
    | _ -> None
  in
  inst f1 f2
;;

(* TODO(Chase): The List.permute is not sustainable as far as I can tell. The
   number of nominals I'm getting in proofs causes too many permutations to
   be generated, causing a stack overflow. Maybe we could move to a [Stream]
   instead of a list?*)
(* Try to unify t1 and t2 under permutations of nominal constants.
   For each successful unification, call sc.
   t1 may contain logic variables, t2 is ground                    *)
let all_meta_right_permute_unify ~sc schemas nvars ctxvar_ctx new_ctxvar_ctx t1 t2 =
  (*  print_endline ("Matching formula "^(Print.string_of_formula t2)^" to formula "^(Print.string_of_formula t1)); *)
  (* We exclude names from context variable blocks in the permutation
     as these are maintained across the sequent and so cannot be renamed within
     a formula *)
  let support_t1 = Formula.formula_support_sans (new_ctxvar_ctx @ ctxvar_ctx) t1 in
  let support_t2 = Formula.formula_support_sans (new_ctxvar_ctx @ ctxvar_ctx) t2 in
  if List.length support_t1 < List.length support_t2
  then (* Ground term cannot have more nominals than logic term *)
    ()
  else (
    let support_t2_names = List.map term_to_name support_t2 in
    support_t1
    |> List.permute (List.length support_t2)
    |> List.iter
         (Term.unwind_state (fun perm_support_t1 ->
              let alist = List.combine support_t2_names perm_support_t1 in
              (* NOTE TO MK: Do I need to check types at all in the permutation? *)
              try
                let subst =
                  formula_instance
                    schemas
                    nvars
                    (List.map
                       (fun (s, cty) -> s, Context.replace_ctx_typ_vars alist cty)
                       ctxvar_ctx)
                    new_ctxvar_ctx
                    t1
                    (Formula.replace_formula_vars alist t2)
                in
                if Option.is_some subst then sc (subst, Term.get_bind_state ())
              with
              | Unify.UnifyFailure _ -> ())))
;;

(* like all_meta_right_permute_unify but only attempts to unify the two context expressions. *)
(* Commenting this out because it's not used
let all_meta_right_permute_unify_ctxexpr ~sc schemas nvars ctxvar_ctx new_ctxvar_ctx g1 g2
  =
  let support_g1 = Formula.context_support_sans (new_ctxvar_ctx @ ctxvar_ctx) g1 in
  let support_g2 = Formula.context_support_sans (new_ctxvar_ctx @ ctxvar_ctx) g2 in
  if List.length support_g1 < List.length support_g2
  then (* Ground term cannot have more nominals than logic term *)
    ()
  else (
    let support_g2_names = List.map term_to_name support_g2 in
    support_g1
    |> List.permute (List.length support_g2)
    |> List.iter
         (Term.unwind_state (fun perm_support_g1 ->
              let alist = List.combine support_g2_names perm_support_g1 in
              (* NOTE TO MK: Do I need to check types at all in the permutation? *)
              try
                let subst =
                  context_instance
                    schemas
                    nvars
                    (List.map
                       (fun (s, cty) -> s, Context.replace_ctx_typ_vars alist cty)
                       ctxvar_ctx)
                    new_ctxvar_ctx
                    g1
                    (Context.replace_ctx_expr_vars alist g2)
                in
                if Option.is_some subst then sc (subst, Term.get_bind_state ())
              with
              | Unify.UnifyFailure _ -> ())))
;;
*)

(* determines if f2 is an instance of formula f1.
   Allowed to instantiate the eigenvariables in f1 but not
   those in f2. *)
(* Commenting this out because it's not used
let instance_of nvars ctxvar_ctx f1 f2 =
  let f1' = Formula.copy_formula f1 in
  all_meta_right_permute_unify ~sc:(fun _ -> raise Success) [] nvars ctxvar_ctx [] f1' f2
;;
*)

(* Given an LF signature, a context expression, and a type
   this function computes
      F(ctx; typ)
   which is the set of atomic formulas whose validity ensure that the
   given type expression is a valid LF type under the given context. *)
let decompose_kinding lf_sig used ctx typ =
  let used = ref used in
  let rec decompose ctx typ =
    match observe (hnorm typ) with
    | Pi (tyctx, ty) ->
      let v, typ = List.hd tyctx in
      let nvar, used' = fresh_wrt ~ts:3 Nominal "n" (erase typ) !used in
      used := used';
      List.append
        (decompose ctx typ)
        (decompose
           (Context.Ctx (ctx, (term_to_var nvar, typ)))
           (replace_term_vars [ v.name, nvar ] (Term.pi (List.tl tyctx) ty)))
    | Var v when v.tag = Constant ->
      if Signature.is_type lf_sig v.name
      then (
        let ty_decl = Signature.lookup_type_decl lf_sig v.name in
        (*We know from given type being well formed at arity type
          o that this constant must have kind Type *)
        assert (ty_decl.kind = Type);
        [])
      else raise (InvalidName v.name)
    | App (h, args) when is_var Constant (observe (hnorm h)) ->
      if Signature.is_type lf_sig (get_id (observe (hnorm h)))
      then (
        let ty_decl = Signature.lookup_type_decl lf_sig (get_id (observe (hnorm h))) in
        let tyargs =
          match ty_decl.Signature.kind with
          | Pi (tyargs, _) -> tyargs
          | _ -> bugf "Expected Pi type"
        in
        let tyargs_args = List.combine tyargs args in
        List.mapi
          (fun i ((_, typ), arg) ->
            let typ' =
              replace_term_vars
                (List.map (fun ((v, _), a) -> v.Term.name, a) (List.take i tyargs_args))
                typ
            in
            Formula.atm ctx arg typ')
          tyargs_args)
      else raise (InvalidName (get_id (observe (hnorm h))))
    | _ -> raise (InvalidTerm typ)
  in
  decompose ctx typ
;;

(* check if the inductive restriction r1 satisfies the
   inductive restriction r2 *)
let satisfies r1 r2 =
  match r1, r2 with
  | (Formula.LT i, Formula.LT j | Formula.LT i, Formula.EQ j | Formula.EQ i, Formula.EQ j)
    when i = j -> true
  | _, Formula.LT _ -> false
  | _, Formula.EQ _ -> false
  | _ -> true
;;

(* Search:
   assumption is that the current goal formula is atomic, or a defined proposition.
   raises Success exception if current goal is determined valid by search.

   procedure:
     1) once at outset check the nominal constants in explicit part of context
   - no duplicate binding for name
   - all explicit bindings must be restricted from appearing in context variables
     2) then being the search loop attempting to complete derivation
          a) normalize the goal formula (i.e. apply Pi-R rule)
          b) check for match in assumption set (i.e. apply id rule)
          c) decompose typing judgement (i.e. apply atm-R rule)
   - for leaves perform check of context formation
                   must either be the prefix of some context expression from an assumption or
                   shown well-formed explicitly

*)
let search ~depth signature sequent =
  (* checks that the explicit bindings in context expression g are all distinct and are
     restricted from appearing in any instance of any context variable appearing in g. *)
  let check_context_names g =
    let explicit_names = List.map (fun (x, _) -> x.Term.name) (Context.get_explicit g) in
    List.is_unique explicit_names
    &&
    if Context.has_var g
    then
      List.for_all
        (fun x ->
          List.mem
            x
            (Sequent.get_ctxvar_restricted
               (Sequent.ctxvar_lookup sequent.ctxvars (Context.get_ctx_var g))))
        explicit_names
    else true
  in
  (* aux function does the meat of this function, searching for derivations of each subgoal in list. *)
  let rec search_aux (subgoals : (unit -> unit) list) =
    (* checks that the context g will be a well-formed LF context for any instance of the sequent.
       Note that whenever this function is called we already have checked the names used for
       explicit bindings, so this check is focused on the formation of the LF types in a context expression. *)
    let rec check_context used g =
      let hyp_ctxexprs =
        List.filter_map
          (fun x ->
            match x.Sequent.formula with
            | Formula.Atm (g, _, _, _) -> Some g
            | _ -> None)
          sequent.Sequent.hyps
      in
      let support_g =
        Formula.context_support_sans (Sequent.get_cvar_tys sequent.ctxvars) g
      in
      (* first, attempts to find an assumption formula with g as a prefix of the context expression. *)
      let match_with_ctx hyp_g =
        if Context.has_var g = Context.has_var hyp_g
        then (
          let support_hypg =
            Formula.context_support_sans (Sequent.get_cvar_tys sequent.ctxvars) hyp_g
          in
          if List.length support_hypg >= List.length support_g
          then (
            let support_g_names = List.map term_to_name support_g in
            support_hypg
            |> List.permute (List.length support_g)
            |> List.iter (fun perm ->
                   let alist = List.combine support_g_names perm in
                   if Context.context_prefix (Context.replace_ctx_expr_vars alist g) hyp_g
                   then raise Success
                   else ()))
          else ())
      in
      List.iter match_with_ctx hyp_ctxexprs;
      (* if matching with assumption context expressions fails, then attempt to check
         the well-formedness explicitly. *)
      match g with
      | Context.Nil -> raise Success
      | Context.Var _ -> ()
      | Context.Ctx (g', (_, typ)) ->
        let save_seq, bind_state = Sequent.cp_sequent sequent, Term.get_bind_state () in
        let subgoals = decompose_kinding signature used g' typ in
        (try
           search_aux
             (List.map
                (fun f () ->
                  Sequent.assign_sequent sequent save_seq;
                  Term.set_bind_state bind_state;
                  sequent.Sequent.goal <- f)
                subgoals)
         with
        | Success -> check_context used g'
        | _ -> ())
    in
    (* put goal formula into normal form *)
    let norm () =
      let goal' = Sequent.norm_atom sequent sequent.goal in
      sequent.goal <- goal'
    in
    (* attempt to apply id proof step by matching with some hypothesis *)
    (* Find a type with applications in the type.
       Look up the head of that type in the signature.
       Create "invisible" hypotheses for the arguments to the type in the hypothesis
       to the types they are assigned in the signature.*)
    let rec extract_tys (f : Formula.formula) (depth_left : int) =
      if depth_left <= 0
      then []
      else (
        match f with
        | Formula.(
            Top | Bottom | Ctx _ | All _ | Exists _ | Imp _ | And _ | Or _ | Prop _) -> []
        | Formula.Atm (ctx, _, ty, _) ->
          (match observe (hnorm ty) with
          | App (head, _) when is_var Constant (observe (hnorm head)) ->
            decompose_kinding signature [] ctx ty
            |> List.flatten_map (fun f -> f :: extract_tys f (depth_left - 1))
          | App _ | Var _ | DB _ | Lam _ | Susp _ | Ptr _ | Pi _ | Type -> []))
    in
    let try_match () =
      let support_goal =
        Formula.formula_support_sans (Sequent.get_cvar_tys sequent.ctxvars) sequent.goal
      in
      let extracted_types =
        List.flatten_map (fun hyp -> extract_tys hyp.formula depth) sequent.hyps
        |> List.map (fun f -> Sequent.make_hyp sequent f)
      in
      List.iter
        (fun h ->
          let f = h.formula in
          (* try each permutation of nominals in assumption formula*)
          match f with
          | Formula.Atm (_, _, _, ann) ->
            if satisfies ann (Formula.formula_to_annotation sequent.goal)
            then (
              let support_hyp =
                Formula.formula_support_sans (Sequent.get_cvar_tys sequent.ctxvars) f
              in
              if List.length support_hyp = List.length support_goal
              then (
                let support_hyp_names = List.map term_to_name support_hyp in
                support_goal
                |> List.permute (List.length support_hyp)
                |> List.iter (fun perm ->
                       let alist = List.combine support_hyp_names perm in
                       (* let _ = print_endline ("search matching formula: "^(Print.string_of_formula (Formula.replace_formula_vars alist (Formula.copy_formula f)))^"\nto formula: "^(Print.string_of_formula sequent.goal)) in *)
                       if Formula.eq
                            (Formula.replace_formula_vars alist (Formula.copy_formula f))
                            sequent.goal
                       then raise Success
                       else ()))
              else ())
            else ()
          | Formula.Prop _ ->
            let support_hyp =
              Formula.formula_support_sans (Sequent.get_cvar_tys sequent.ctxvars) f
            in
            if List.length support_hyp = List.length support_goal
            then (
              let support_hyp_names = List.map term_to_name support_hyp in
              support_goal
              |> List.permute (List.length support_hyp)
              |> List.iter (fun perm ->
                     let alist = List.combine support_hyp_names perm in
                     (* let _ = print_endline ("search matching formula: "^(Print.string_of_formula (Formula.replace_formula_vars alist (Formula.copy_formula f)))^"\nto formula: "^(Print.string_of_formula sequent.goal)) in *)
                     if Formula.eq
                          (Formula.replace_formula_vars alist (Formula.copy_formula f))
                          sequent.goal
                     then raise Success
                     else ()))
            else ()
          | _ -> ())
        (sequent.hyps @ extracted_types)
    in
    (* use atm-R to make a reasoning step. *)
    let lf_step () =
      (* function for constructing the subgoals which might be generated by this step. *)
      let make_subgoals g ann args bndrs body =
        let rec mk_sg args bndrs =
          match args, bndrs with
          | [], [] -> []
          | [ arg ], bndrs when List.length bndrs > 1 ->
            (* arg : pi(bndrs,body) *)
            let subgoal =
              let _ = Sequent.cp_sequent sequent in
              fun () -> sequent.goal <- Formula.Atm (g, arg, pi bndrs body, ann)
            in
            [ subgoal ]
          | arg :: args', (v, ty) :: bndrs' ->
            let subgoal =
              let _ = Sequent.cp_sequent sequent in
              fun () -> sequent.goal <- Formula.Atm (g, arg, ty, ann)
            in
            subgoal
            :: mk_sg
                 args'
                 (List.map
                    (fun (b, ty) -> b, Term.replace_term_vars [ v.name, arg ] ty)
                    bndrs')
          | [], _ | _, [] -> bugf "Expected two have same number of args as binders"
        in
        mk_sg args bndrs
      in
      (* Note: Since this is analysis is always performed after normalization we 
               are assured that the type of the judgement is atomic and the head of the 
               term component of the judgement is a variable or an application term. *)
      let g, m, a, ann =
        match sequent.goal with
        | Formula.Atm (g, m, a, ann) -> g, m, a, ann
        | _ -> bugf "Expected atomic form"
      in
      match Term.observe (Term.hnorm m) with
      | (Term.Var _ as h) | Term.App (h, []) ->
        (* leaf analysis in this case *)
        let _, _, hd_ty =
          match Term.observe (Term.hnorm h) with
          | Term.Var v when v.tag = Term.Constant ->
            (* Freshen the type from the signature to ensure that *)
            (* the names bound by Pis are all fresh. *)
            (Signature.lookup_obj_decl signature v.name).Signature.typ
            |> Term.hnorm
            |> freshen_type ~used:sequent.vars ~support:[]
          | Term.Var v when v.tag = Term.Nominal ->
            (* Freshen the type from the context to ensure that *)
            (* the names bound by Pis are all fresh. *)
            List.assoc v (Context.ctxexpr_to_ctx (Sequent.get_cvar_tys sequent.ctxvars) g)
            |> Term.hnorm
            |> freshen_type ~used:sequent.vars ~support:[]
          | Term.Var _ -> bugf "Expected constant or nominal"
          | _ -> bugf "Head of term expected to be a variable"
        in
        (try
           if Term.eq hd_ty a
           then
             check_context
               (Formula.get_formula_used_nominals
                  (Sequent.get_cvar_tys sequent.ctxvars)
                  sequent.goal)
               g
           else ()
         with
        | Success -> raise Success
        | _ -> ())
      | Term.App (h, args) ->
        (* will raise exception if does not match, which is correct behavior
           as goals with terms that do not match this structure (i.e. head is a term variable)
           lead to a search failure as no proof rule will apply. *)
        let new_tms, new_lftys, target_ty =
          match Term.observe (Term.hnorm h) with
          | Term.Var v when v.tag = Term.Constant ->
            (* Freshen the type from the signature to ensure that *)
            (* the names bound by Pis are all fresh. *)
            (Signature.lookup_obj_decl signature v.name).Signature.typ
            |> Term.hnorm
            |> freshen_type ~used:sequent.vars ~support:[]
          | Term.Var v when v.tag = Term.Nominal ->
            (* Freshen the type from the context to ensure that *)
            (* the names bound by Pis are all fresh. *)
            List.assoc v (Context.ctxexpr_to_ctx (Sequent.get_cvar_tys sequent.ctxvars) g)
            |> Term.hnorm
            |> freshen_type ~used:sequent.vars ~support:[]
          | Term.Var _ -> bugf "Expected constant or nominal"
          | _ -> bugf "Head of term expected to be a variable"
        in
        let hd_ty =
          pi (List.map2 (fun t ty -> Term.term_to_var t, ty) new_tms new_lftys) target_ty
        in
        (try
           match Term.observe (Term.hnorm hd_ty) with
           | Term.Pi (bndrs, body) ->
             if Term.eq (Term.app hd_ty args) a
             then (
               let new_subgoals = make_subgoals g ann args bndrs body in
               search_aux new_subgoals)
             else ()
           | _ -> ()
         with
        | Success -> raise Success
        | _ -> ())
      | _ -> ()
    in
    match subgoals with
    | [] -> raise Success
    | hd :: tl ->
      hd ();
      (try
         norm ();
         try_match ();
         lf_step ()
       with
      | Success -> search_aux tl
      | _ -> ())
  in
  match sequent.goal with
  | Formula.Atm (g, _, _, _) ->
    if check_context_names g then search_aux [ (fun () -> ()) ] else ()
  | Formula.Prop _ -> search_aux [ (fun () -> ()) ]
  | _ -> ()
;;

(* Given a sequent and an integer identifying which subformula to
 * induct on, returns an updated sequent with annotations added and 
 * inductive hypothesis in the assumptions.
 * Raises InvalidFormula if the identified subformula is not atomic.
 *)
let ind_count = ref 0

let get_ind_count () =
  let _ = ind_count := 1 + !ind_count in
  !ind_count
;;

let reset_ind_count () = ind_count := 0

let ind sequent i =
  let rec mk_ih form i =
    match form with
    | Formula.Imp (l, r) when i = 1 ->
      let aux f =
        match f with
        | Formula.Atm (g, m, a, ann) ->
          if ann = Formula.None
          then (
            let num = get_ind_count () in
            ( Formula.Imp (Formula.Atm (g, m, a, Formula.LT num), r)
            , Formula.Imp (Formula.Atm (g, m, a, Formula.EQ num), r) ))
          else
            raise (InvalidFormula (sequent.goal, "Cannot induct on annotated formulas."))
        | _ ->
          raise
            (InvalidFormula
               (sequent.goal, "Formula must be an atomic assumption for induction"))
      in
      aux l
    | Formula.Imp (l, r) ->
      let ih, goal = mk_ih r (i - 1) in
      Formula.Imp (l, ih), Formula.Imp (l, goal)
    | Formula.All (var, f) ->
      let ih, goal = mk_ih f i in
      Formula.All (var, ih), Formula.All (var, goal)
    | Formula.Ctx (vs, f) ->
      let ih, goal = mk_ih f i in
      Formula.Ctx (vs, ih), Formula.Ctx (vs, goal)
    | Formula.Atm _ -> raise (InvalidFormula (sequent.goal, "Induction index too large."))
    | _ ->
      raise (InvalidFormula (sequent.goal, "Formula not of valid form for induction."))
  in
  let ih, goal = mk_ih sequent.goal i in
  (* need to unlink the IH variables from goal formula *)
  let ih' = Formula.copy_formula ih in
  add_hyp sequent ~name:"IH" ih';
  sequent.goal <- goal
;;

(* adds a new instance of block schema bl_schm at position j in the 
   explicit blocks in tycvar using nominal constants names for the
   bound variables and identifies the i-th entry in this new block
   instance.

   assumptions:
   - seq is a well-formed sequent (N; Psi; Xi: Omega ---> F)
   - tycvar is (Gamma|NGamma : C[G1;...;Gn]) is in Xi
   - bl_schm is a block schema {x1:a1,...,xn:an}y1:A1,...,yl:Ak of C
   - usable is a subset of (N \ NGamma)
   - names is a list (n1, ...,nk) of distinct names, different from
       usable, and for 1<= l <= k, nl:(Al)- is in (Noms \NGamma)
   - we further assume that 1<=i<=k and 0<=j<=n

   "addBlock seq tycvar bl_schm names usable j i"

   returns the tuple
    <(N U names;Psij' U Psij'';Xij'; Omega[thetaj'] ---> F[thetaj']),
       ni:Ai[thetaj'']> 
   where
   - Nj is the collection of nominal constants assigned types in
      (G1,...,Gj)
   - Psij' is a version of Psi raised over {n1,...,nk}\N, and
      thetaj' is the associated raising substitution 
   - Psij'' is a version of {x1:a1,...,xn:an} raised over
      usable U Nj U {n1,...,nk}
      with new variables chosen to be distinct from those in Psij',
      and thetaj'' is the associated raising substitution
   - G is the context expression (n1:A1[thetaj''],...,nk:Ak[thetaj''])
   - Xij' is the context variable context
       (Xi\tycvar)[thetaj'] U
         {Gamma|NGamma:C[G1[thetaj'];...;Gj[thetaj'];G;G{j+1}[thetaj'];...;Gn[thetaj']]}*)
(* Possible raising optimization:
     in Psij' we might check which variables in Psi have a rigid
     occurence in G1,...,Gj and avoid raising these variables because 
     such dependencies would be ill-formed. *)
let addBlock
    (seq : Sequent.sequent)
    (tycvar : Sequent.cvar_entry)
    (bl_schm : Context.block_schema)
    (names : Term.term list)
    (usable : Term.term list)
    (j : int)
    (i : int)
    : Sequent.sequent * Term.term * Term.term
  =
  let seq = Sequent.cp_sequent seq in
  (* generating raised eigenvariable context and raising substitution *)
  let psi = Sequent.get_eigen seq in
  let new_names =
    Sequent.get_nominals seq |> List.map snd |> List.minus ~cmp:Term.eq names
  in
  let psij' =
    if new_names = []
    then psi
    else
      List.map
        (fun (id, tm) ->
          id, Term.var Term.Eigen id 1 (Formula.raise_type new_names (Term.get_var_ty tm)))
        psi
  in
  let thetaj' = List.map2 (fun (id, _) (_, tm) -> id, Term.app tm new_names) psi psij' in
  (* generating the new block and related eigenvariable context *)
  let (Context.B (schema_vars, entries)) = bl_schm in
  let (Context.CtxTy (_, blocks)) = Sequent.get_ctxvar_ty tycvar in
  let pre_blocks = List.take j blocks in
  let nj = List.flatten pre_blocks |> List.map (fun (v, _) -> Term.var_to_term v) in
  let thetaj'', psij'' =
    Formula.fresh_raised_alist
      ~tag:Eigen
      ~used:seq.Sequent.vars
      ~ts:1
      ~support:(usable @ nj @ names)
      schema_vars
  in
  let sch_ids, sch_typs = List.split entries in
  let nominal_inst = List.combine (List.map (fun v -> v.Term.name) sch_ids) names in
  let g =
    List.map2
      (fun n lfty ->
        ( Term.term_to_var n
        , replace_term_vars thetaj'' (replace_term_vars nominal_inst lfty) ))
      names
      sch_typs
  in
  (* constructing the sequent to return *)
  let _ = List.iter (Sequent.add_var seq) (List.map Term.term_to_pair new_names) in
  let _ = List.iter (Sequent.add_var seq) psij' in
  let _ = Sequent.replace_seq_vars thetaj' seq in
  let _ = List.iter (Sequent.add_var seq) (List.map Term.term_to_pair psij'') in
  let _, _, Context.CtxTy (schema, blocks) =
    Sequent.ctxvar_lookup seq.ctxvars (Sequent.get_ctxvar_id tycvar)
  in
  let _ =
    Sequent.remove_ctxvar seq (Sequent.get_ctxvar_id tycvar);
    Sequent.add_ctxvar
      seq
      (Sequent.get_ctxvar_id tycvar)
      ~rstrct:(Sequent.get_ctxvar_restricted tycvar)
      (Context.CtxTy (schema, List.take j blocks @ [ g ] @ List.drop j blocks))
  in
  (* returning heads tuple *)
  let ni, ai = List.nth g i in
  Sequent.cp_sequent seq, Term.var_to_term ni, ai
;;

(* enumerates all the name choices of arity types atys relative to
   names and away from prohibited.
 *)
let rec namesLists
    (atys : Type.ty list)
    (names : Term.term list)
    (prohibited : Term.term list)
    : Term.term list list
  =
  match atys with
  | [] -> [ [] ]
  | a :: atys' ->
    let new_name =
      fst
        (fresh_wrt
           ~ts:2
           Nominal
           "n"
           a
           (List.map Term.term_to_pair (List.append names prohibited)))
    in
    let avail_choices =
      List.minus ~cmp:Term.eq names prohibited
      |> List.filter (fun v -> Term.get_var_ty v = a)
    in
    let pick n = namesLists atys' names (n :: prohibited) |> List.map (fun l -> n :: l) in
    List.map pick (new_name :: avail_choices) |> List.flatten
;;

(* determines (sequent, head) tuples for introducing a new block
   following bl_schm into the context variable type of tycvar using
   each possible ordering.

   assuming:
   - seq is a well-formed sequent (N; Psi; Xi: Omega ---> F)
   - tycvar is (Gamma|NGamma : C[G1;...;Gn]) is in Xi
   - bl_schm is a block schema {x1:a1,...,xn:an}y1:A1,...,yl:Ak of C
   - g is a context expression (appearing somewhere in seq) that
       contains the context variable Gamma

   "allBlocks seq g tycvar bl_schm"

   returns the set
    {AddBlock seq tycvar bl_schm names usable j i |
          0<= j<= n,
          1<= i<= k,
          names is in (namesLists [(A1)-;...;(Ak)-] usable (NGamma U prohibited))}
   where
   - prohibited is the collection of nominal constants assigned types
      by the explicit bindings of g relative to seq
   - usable is the collection of nominal constants (N \ NGamma \ prohibited)
 *)
let allBlocks
    (seq : Sequent.sequent)
    (g : Context.ctx_expr)
    (tycvar : Sequent.cvar_entry)
    (bl_schm : Context.block_schema)
    : (Sequent.sequent * Term.term * Term.term) list
  =
  let (Context.B (_, entries)) = bl_schm in
  let entry_atys = List.map (fun (v, _) -> v.ty) entries in
  let noms = Sequent.get_nominals seq in
  let n_gamma =
    List.map (fun n -> List.assoc n noms) (Sequent.get_ctxvar_restricted tycvar)
  in
  let prohibited =
    Context.ctxexpr_to_ctx (Sequent.get_cvar_tys seq.ctxvars) g
    |> List.map (fun (v, _) -> Term.var_to_term v)
  in
  let usable =
    List.minus
      ~cmp:Term.eq
      (List.minus ~cmp:Term.eq (List.map snd noms) n_gamma)
      prohibited
  in
  (* for each location in the block list j
         0 to 
           (let CtxTy(schema, blocks) = Sequent.get_ctxvar_ty tycvar in
            List.length blocks)
     for every list of names in namelsts names,
     for every binding in the block i
         1 to (List.length entries),
     call:
     addblock seq tycvar bl_schm names usable j i *)
  let namelsts = namesLists entry_atys usable (n_gamma @ prohibited) in
  let (Context.CtxTy (_, blocks)) = Sequent.get_ctxvar_ty tycvar in
  let js = List.range 0 (List.length blocks) in
  let is = List.range 0 (List.length entries - 1) in
  List.map
    (fun j ->
      List.map
        (fun names ->
          List.map
            (fun i -> addBlock seq tycvar bl_schm names (List.minus usable names) j i)
            is)
        namelsts
      |> List.flatten)
    js
  |> List.flatten
;;

(* implicitHeads returns all (sequent, head) tuples for matching with
   some as-yet unidentified binding in the context variable.

   assuming:
   - seq is a well-formed sequent (N; Psi; Xi: Omega ---> F)
   - g is a context expression (appearing somewhere in seq) that
       contains a context variable Gamma and Gamma|NGamma:C[G1,...,Gn]
       is in Xi
   - bl_schm1,...,bl_schmm is the collection of block schemas
       comprising schema C in schemas

   "implicitHeads seq schemas g"

   returns the set
       U{allBlocks seq g tycvar bl_schmi | 1<= i<= m}
   where
   - tycvar = Gamma|NGamma:C[G1,...,Gn]
 *)
let implicitHeads seq schemas (g : Context.ctx_expr)
    : (Sequent.sequent * Term.term * Term.term) list
  =
  let gamma = Context.get_ctx_var g in
  let tycvar = Sequent.ctxvar_lookup seq.ctxvars gamma in
  let (Context.CtxTy (schema, _)) = Sequent.get_ctxvar_ty tycvar in
  let block_schemas = List.assoc schema schemas in
  List.map (allBlocks seq g tycvar) block_schemas |> List.flatten
;;

(* returns the tuple (seq, n:A) for each explicit binding in g
   relative to seq.*)
let explicitHeads seq g : (Sequent.sequent * Term.term * Term.term) list =
  let explct_bnds = Context.ctxexpr_to_ctx (Sequent.get_cvar_tys seq.ctxvars) g in
  List.map (fun (h, ty) -> seq, Term.var_to_term h, ty) explct_bnds
;;

let sigHeads lf_sig seq : (Sequent.sequent * Term.term * Term.term) list =
  let objs = Signature.get_obj_decls lf_sig in
  List.map
    (fun obj ->
      ( seq
      , Term.const obj.Signature.obj_name (Term.erase obj.Signature.typ)
      , obj.Signature.typ ))
    objs
;;

(* returns all the (sequent, head) tuples identified for the context
   expression g relative to seq.  *)
let heads lf_sig schemas seq g =
  let sig_heads = sigHeads lf_sig seq in
  let ex_heads = explicitHeads seq g in
  if Context.has_var g
  then sig_heads @ ex_heads @ implicitHeads seq schemas g
  else sig_heads @ ex_heads
;;

(* generates and adds cases for the head h:typ
   Auumes that the given formula atomic formula and that it actually
   appears as an assumption in the given sequent.

   Note that the unification procedure we use returns at most one 
   unifier, so either an empty (non-unifiable) or a singleton list is
   returned. *)
let makeCases form seq (h : Term.term) typ : case list =
  match form with
  | Formula.Atm (g, m, a, ann) ->
    let save_seq, bind_state = Sequent.cp_sequent seq, Term.get_bind_state () in
    let new_tms, new_lftys, genty =
      freshen_type
        ~used:seq.Sequent.vars
        ~support:(Sequent.get_nominals seq |> List.map snd)
        (observe (hnorm typ))
    in
    let gentm = app h new_tms in
    (match
       Unify.try_left_unify_list_cpairs ~used:seq.Sequent.vars [ genty; gentm ] [ a; m ]
     with
    | Some [] ->
      Formula.get_formula_used (Sequent.get_cvar_tys seq.ctxvars) form
      @ Formula.get_formula_used_nominals (Sequent.get_cvar_tys seq.ctxvars) form
      |> List.iter (fun (_, t) -> Sequent.add_var seq (term_to_pair t));
      let new_hyps =
        List.map2
          (fun t ty -> Formula.Atm (g, t, ty, Formula.reduce_inductive_annotation ann))
          new_tms
          new_lftys
      in
      List.iter (Sequent.add_hyp seq) new_hyps;
      let case = make_case seq in
      Sequent.assign_sequent seq save_seq;
      Term.set_bind_state bind_state;
      [ case ]
    | None ->
      Sequent.assign_sequent seq save_seq;
      Term.set_bind_state bind_state;
      []
    | _ ->
      Sequent.assign_sequent seq save_seq;
      Term.set_bind_state bind_state;
      raise NotLlambda)
  | _ -> bugf "Expected atomic formula when making cases"
;;

(* Given a sequent and a name identifying an assumption formula,
 * of the sequent this will perform case analysis on the
 * identified subgoal and will return the updated sequent and list
 * of new subgoals if any.
 * Raises InvalidName if the name provided does not match a hypothesis 
 * in the sequent.
 * Raises InvalidFormula if the identified assumption is not atomic
 * with a base type.
 * Raises NotLlambda if unification cannot be completed.
 *)
let cases lf_sig schemas seq id : case list =
  let hyp =
    try get_hyp seq id with
    | Not_found -> raise (InvalidName id)
  in
  let g, _, a, _ =
    match hyp.formula with
    | Formula.Atm (g, m, a, ann) -> g, m, a, ann
    | _ -> raise (InvalidFormula (hyp.formula, "Formula must be atomic."))
  in
  let ty_head =
    match Term.norm a with
    | Var v when v.tag = Constant ->
      ignore @@ Signature.lookup_type_decl lf_sig v.name;
      v.name
    | App (h, _) ->
      (match Term.norm h with
      | Var v when v.tag = Constant ->
        ignore @@ Signature.lookup_type_decl lf_sig v.name;
        v.name
      | _ ->
        raise
          (InvalidFormula
             (hyp.formula, "Atomic formula must have a base type typing judgment.")))
    | _ ->
      raise
        (InvalidFormula
           (hyp.formula, "Atomic formula must have a base type typing judgment."))
  in
  let case_heads =
    heads lf_sig schemas seq g
    |> List.filter (fun (_, _, typ) -> Term.get_ty_head typ = ty_head)
  in
  let per_head (seq, h, typ) =
    (* let (save_seq,bind_state) = (Sequent.cp_sequent seq, Term.get_bind_state ()) in *)
    let hyp = get_hyp seq id in
    let case = makeCases hyp.Sequent.formula seq h typ in
    (* let _ = Sequent.assign_sequent seq save_seq; *)
    (*         Term.set_bind_state bind_state in *)
    case
  in
  List.map per_head case_heads |> List.flatten
;;

(* Given a sequent and a term, checks that the term is weakly well
 * formed of the appropriate weak type and then instantiates the 
 * goal formula with that term and returns the updated sequent.
 * Raises InvalidTerm if the term is not weakly well typed.
 *)
let exists sequent t =
  let got_ty = Typing.infer_ty [] t in
  match sequent.goal with
  | Formula.Exists ([ (n, ty) ], body) ->
    if Type.eq got_ty ty
    then
      sequent.goal <- Formula.replace_formula_vars_rename ~used:sequent.vars [ n, t ] body
    else raise (InvalidTerm t)
  | Formula.Exists ((n, ty) :: vs, body) ->
    if Type.eq got_ty ty
    then
      sequent.goal
        <- Formula.replace_formula_vars_rename
             ~used:sequent.vars
             [ n, t ]
             (Formula.Exists (vs, body))
    else raise (InvalidTerm t)
  | _ -> assert false
;;

(* Apply one statement to a list of other statements *)

let check_restrictions formal actual =
  if List.length formal <> List.length actual
  then
    failwithf
      "%s arguments to apply\n(Expected %d but got %d)"
      (let diff = compare (List.length formal) (List.length actual) in
       if diff > 0 then "Not enough" else "Too many")
      (List.length formal)
      (List.length actual);
  List.iter2
    (fun fr ar ->
      match fr, ar with
      | Formula.LT i, Formula.LT j when i = j -> ()
      | Formula.EQ i, Formula.LT j when i = j -> ()
      | Formula.EQ i, Formula.EQ j when i = j -> ()
      | Formula.None, _ -> ()
      | _ -> failwith "Inductive restriction violated")
    formal
    actual
;;

let rec map_args f t =
  match t with
  | Formula.Imp (left, right) -> f left :: map_args f right
  | _ -> []
;;

let apply_arrow schemas sequent nvars ctxvar_ctx bound_ctxvars form args =
  let () =
    check_restrictions
      (map_args Formula.formula_to_annotation form)
      (List.map Formula.formula_to_annotation args)
  in
  let result =
    List.fold_left
      (fun term arg ->
        match term, arg with
        | Formula.Imp (left, right), arg ->
          let res = ref (None, Term.get_bind_state ()) in
          (* If formula has any existential quantifiers at the top *)
          (* level, or is atomic we should normalize before trying *)
          (* to match with the argument formula. *)
          let rec norm f =
            match f with
            | Formula.Exists (exists, body) ->
              norm
                (freshen_nameless_bindings
                   ~support:(List.map snd nvars)
                   ~ts:1
                   exists
                   body)
            | _ -> Sequent.norm_atom sequent f
          in
          let left = norm left in
          (* check if left has annotation & ensure arg
               can satisfy it *)
          if satisfies
               (Formula.formula_to_annotation arg)
               (Formula.formula_to_annotation left)
          then (
            try
              all_meta_right_permute_unify
                ~sc:(fun x ->
                  res := x;
                  raise Success)
                schemas
                nvars
                ctxvar_ctx
                bound_ctxvars
                left
                arg
            with
            | Success -> ());
          (match !res with
          | Some ctx_subst, bind_state ->
            Term.set_bind_state bind_state;
            Formula.replace_ctx_vars ctx_subst right
          | None, _ -> raise (Unify.UnifyFailure Unify.Generic))
        | _ -> failwith "Too few implications in application")
      form
      args
  in
  Formula.norm result
;;

(* Given a sequent, a formula, and a list of formula args
 * will apply the formula to the given hypotheses (inferring
 * instantiations for universal and context quantifiers)
 * and adds the resulting formula to the sequent. *)
let apply schemas sequent formula args =
  let process_bindings ctxs foralls body =
    let new_ctxvars, body' =
      freshen_ctx_bindings (List.map Sequent.get_ctxvar_id sequent.ctxvars) ctxs body
    in
    let nvars = List.filter (fun (_, t) -> is_var Nominal t) sequent.vars in
    apply_arrow
      schemas
      sequent
      nvars
      (Sequent.get_cvar_tys sequent.ctxvars)
      new_ctxvars
      (freshen_nameless_bindings ~support:(List.map snd nvars) ~ts:1 foralls body')
      args
  in
  let rec collect_bindings ctxbndrs varbndrs formula =
    match Formula.norm formula with
    | Formula.Ctx (bndrs, body) -> collect_bindings (ctxbndrs @ bndrs) varbndrs body
    | Formula.All (vs, body) -> collect_bindings ctxbndrs (varbndrs @ vs) body
    | Formula.Imp (_, _) -> ctxbndrs, varbndrs, formula
    | _ ->
      [ "Structure of applied term must be a substructure of the following."
      ; "<ctx/forall quantifiers> F1 => ... => Fk => F"
      ]
      |> String.concat "\n"
      |> failwith
  in
  let ctxbndrs, varbndrs, body = collect_bindings [] [] formula in
  process_bindings ctxbndrs varbndrs body
;;

let take_from_binders binders withs =
  let withs' = List.find_all (fun (x, _) -> List.mem_assoc x binders) withs in
  let binders' = List.remove_all (fun (x, _) -> List.mem_assoc x withs) binders in
  binders', withs'
;;

let take_from_ctxbinders ctxbinders withs =
  let withs' = List.find_all (fun (x, _) -> List.mem_assoc x ctxbinders) withs in
  let binders' = List.remove_all (fun (x, _) -> List.mem_assoc x withs) ctxbinders in
  binders', withs'
;;

(* Instantiates universal and context quantifiers using withs provided.
   Assumes type checking has already been done, i.e. if (X,t) is in withs
   then the type of term t should match the (weak) type of X in the binder. *)
let rec instantiate_withs term (vwiths, cwiths) =
  match term with
  | Formula.All (idtys, f) ->
    let binders', withs' = take_from_binders idtys vwiths in
    let body =
      instantiate_withs (Formula.replace_formula_vars withs' f) (vwiths, cwiths)
    in
    Formula.norm (Formula.forall binders' body)
  | Formula.Ctx (cvartys, f) ->
    let binders', withs' = take_from_ctxbinders cvartys cwiths in
    let body = instantiate_withs (Formula.replace_ctx_vars withs' f) (vwiths, cwiths) in
    Formula.norm (Formula.ctx binders' body)
  | _ -> term
;;

let apply_with schemas sequent formula args (vwiths, cwiths) =
  if args = [] && vwiths = [] && cwiths = []
  then formula
  else (
    let term = instantiate_withs formula (vwiths, cwiths) in
    apply schemas sequent (Formula.norm term) args)
;;

(* match (Formula.norm term) with *)
(* | Formula.Imp(_,_) as f -> *)
(*    apply schemas sequent f args *)
(* | f when args = [] -> *)
(*    apply schemas sequent f args  *)
(* | f -> *)
(*    apply schemas sequent f args *)
(*       (failwith "All quantifier instantiations must be given before applying to formulas.") *)

(* Given a sequent, applies one of:  ctx-R, all-R, and imp-R and
 * returns the resulting sequent. *)
let intro sequent =
  match sequent.goal with
  | Formula.Imp (l, r) ->
    let hyp = norm sequent l in
    add_hyp sequent hyp;
    sequent.goal <- r
  | Formula.All (vs, f) ->
    let support =
      List.map snd (List.filter (fun (_, t) -> Term.is_var Term.Nominal t) sequent.vars)
    in
    let used = ref (List.filter (fun (_, t) -> Term.is_var Term.Eigen t) sequent.vars) in
    let new_vars =
      List.map
        (fun (n, ty) ->
          let t, used' =
            Term.fresh_wrt ~ts:1 Term.Eigen n (Formula.raise_type support ty) !used
          in
          used := used';
          Term.get_id t, t)
        vs
    in
    List.iter (add_var sequent) new_vars;
    sequent.goal
      <- Formula.replace_formula_vars
           (List.map2 (fun (n, _) (_, t) -> n, Term.app t support) vs new_vars)
           f
  | Formula.Ctx (cvars, f) ->
    let cvars' = List.map (fun (v, id) -> v, ref [], Context.ctx_typ ~id ()) cvars in
    sequent.ctxvars <- cvars' @ sequent.ctxvars;
    sequent.goal <- f
  | _ -> raise (InvalidFormula (sequent.goal, "Cannot introduce further."))
;;

(* Like intro but applies all ctx-R, all-R, and imp-R possible to the
 * given sequent. *)
let rec intros s =
  try
    intro s;
    intros s
  with
  | InvalidFormula _ -> ()
;;

let split = function
  | Formula.And (g1, g2) -> g1, g2
  | f -> raise (InvalidFormula (f, "Formula not a conjunction."))
;;

let left = function
  | Formula.Or (l, _) -> l
  | f -> raise (InvalidFormula (f, "Formula not a disjunction."))
;;

let right = function
  | Formula.Or (_, r) -> r
  | f -> raise (InvalidFormula (f, "Formula not a disjunction."))
;;

let weaken ~depth lf_sig sequent form t =
  let used = List.filter (fun (_, t) -> Term.is_var Term.Nominal t) sequent.vars in
  match form with
  | Formula.Atm (g, _, _, _) ->
    (* 1. save current state.
        2. for each goal formula, set as sequent goal and search. *)
    let save_seq, bind_state = Sequent.cp_sequent sequent, Term.get_bind_state () in
    let rec solve_goals = function
      | [] ->
        Sequent.assign_sequent sequent save_seq;
        Term.set_bind_state bind_state;
        raise Success
      | g :: goals ->
        (try
           Sequent.assign_sequent sequent save_seq;
           Term.set_bind_state bind_state;
           sequent.Sequent.goal <- g;
           search ~depth lf_sig sequent
         with
        | Success -> solve_goals goals)
    in
    solve_goals (decompose_kinding lf_sig used g t)
  | _ -> raise (InvalidFormula (form, "Formula must be atomic to weaken."))
;;

exception InvalidCtxPermutation of string

let permute_ctx form g' =
  (* need to verify that
       (1) all items in g are in g' and all in g ' are in g
       (2) g' respects dependencies (i.e. no name is used
     in a type before it appears in the context) *)
  let rec check_dependencies = function
    | [], [] -> ()
    | v :: vs, _ :: typs ->
      if List.mem v.Term.name (List.map fst (Term.get_used typs))
      then raise (InvalidCtxPermutation "Later contet items cannot depend on later name");
      check_dependencies (vs, typs)
    | _ -> bugf "Could not check dependencies"
  in
  match form with
  | Formula.Atm (g, m, a, ann) ->
    let g_used_ctxvars = Context.get_used_ctxvars [ g ] in
    let g'_used_ctxvars = Context.get_used_ctxvars [ g' ] in
    if not (List.length g_used_ctxvars = List.length g'_used_ctxvars)
    then
      raise
        (InvalidCtxPermutation
           "context expression must contain the same number of context variables.");
    List.iter
      (fun cvar ->
        if not (List.mem cvar g'_used_ctxvars)
        then raise (InvalidCtxPermutation "contexts must use same context variables")
        else ())
      g_used_ctxvars;
    let g_explicit = Context.get_explicit g in
    let g'_explicit = Context.get_explicit g' in
    if not (List.length g_explicit = List.length g'_explicit)
    then
      raise (InvalidCtxPermutation "explicit portion of context must be the same length.");
    List.iter
      (fun g'_entry ->
        if not (List.exists (fun g_entry -> Context.entry_eq g_entry g'_entry) g_explicit)
        then (
          let v, _ = g'_entry in
          raise
            (InvalidCtxPermutation
               ("not found: " ^ v.Term.name ^ ". all entried must be in both contexts")))
        else ())
      g'_explicit;
    check_dependencies (List.split g'_explicit);
    Formula.atm ~ann g' m a
  | _ -> bugf "Expected atomic formula when permuting context"
;;

let strengthen ctxvars form =
  match form with
  | Formula.Atm (Context.Ctx (g, (v, _)), m, a, ann) ->
    let used =
      Formula.formula_support (Sequent.get_cvar_tys ctxvars) (Formula.Atm (g, m, a, ann))
    in
    if List.exists (fun t -> Term.term_to_name t = v.Term.name) used
    then None
    else Some (Formula.Atm (g, m, a, ann))
  | _ -> bugf "Expected atomic formula when strengthening"
;;

exception InstTypeError of Formula.formula

(* currently we assume that only one instantiation is given.
   This has been checked in the prover before calling this tactic. *)
let inst ~depth lf_sig sequent form subst =
  match form, subst with
  | Formula.Atm (g, m, a, _), [ (n, t) ] ->
    (* split the context g based on location on n into g1,n:b,g2.
          search for a proof that under g1 the term t has type b.
          if successful replace n with t in g2, m, and a and return the
          updated formula. *)
    let save_seq, bind_state = Sequent.cp_sequent sequent, Term.get_bind_state () in
    let g1, b, g2 = Context.split_ctx g n in
    let to_prove = Formula.Atm (g1, t, b, Formula.None) in
    (try
       Term.set_bind_state bind_state;
       sequent.Sequent.goal <- to_prove;
       search ~depth lf_sig sequent;
       raise (InstTypeError to_prove)
     with
    | Success ->
      let _ =
        Sequent.assign_sequent sequent save_seq;
        Term.set_bind_state bind_state
      in
      let g2' =
        List.map
          (fun (id, ty) -> id, Term.replace_term_vars ~tag:Term.Nominal subst ty)
          g2
      in
      let g' = Context.append_context g1 g2' in
      let m' = Term.replace_term_vars ~tag:Term.Nominal subst m in
      let a' = Term.replace_term_vars ~tag:Term.Nominal subst a in
      Formula.Atm (g', m', a', Formula.None))
  | _, _ -> bugf "Expected atomic formula with list of pairs in instantiation"
;;

(* Prune will identify dependencies which are impossible given the restriction
   on the nominal constants which may appear in an instantiation for a
   context variable. *)
let prune sequent form =
  match form with
  | Formula.Atm (g, m, _, _) ->
    if Context.has_var g
    then (
      let hd, args =
        let h = Term.norm m in
        match h with
        | Term.App (hd, args) -> hd, args
        | _ -> bugf "Expected application when pruning"
      in
      let gamma = Context.get_ctx_var g in
      let cvar = Sequent.ctxvar_lookup sequent.ctxvars gamma in
      let bound_names =
        List.map
          (fun (v, _) -> v.Term.name)
          (Context.ctxexpr_to_ctx (Sequent.get_cvar_tys sequent.ctxvars) g)
      in
      let restricted = List.minus (Sequent.get_ctxvar_restricted cvar) bound_names in
      if restricted = []
      then ()
      else (
        let (Type.Ty (atys, id)) = Term.get_var_ty hd in
        let ns = List.map Term.eta_normalize args in
        let to_prune = List.map (fun t -> List.mem (Term.get_id t) restricted) args in
        let args' =
          List.combine to_prune ns
          |> List.filter (fun (v, _) -> not v)
          |> List.map (fun (_, v) -> Term.nominal_var (Term.get_id v) (Term.get_var_ty v))
        in
        let atys' =
          List.combine to_prune atys |> List.filter (fun (v, _) -> not v) |> List.map snd
        in
        let new_ty = Type.Ty (atys', id) in
        let new_term = Term.var Eigen (Term.get_id hd) 1 new_ty in
        let subst =
          [ ( Term.get_id hd
            , List.fold_left
                (fun body n -> abstract (Term.get_id n) (Term.get_var_ty n) body)
                (Term.app new_term args')
                (List.rev ns) )
          ]
        in
        Sequent.add_var sequent (Term.get_id hd, new_term);
        Sequent.replace_seq_vars subst sequent))
    else ()
  | _ -> bugf "Expected pruning atomic formula"
;;
