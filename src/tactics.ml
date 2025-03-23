open Term
open Sequent
open Extensions

type ctx_subst = Context.ctx_var * Context.ctx_expr

(* When an identified formula is of the wrong form.
 * Formula is the invalid formula and string describes what is
 * improper about its form. *)
exception InvalidFormula of Formula.formula * string
exception InvalidTerm of term

(* When a given name is invalid i.e. does not refer to a hypothesis in
 * the current sequent.
 * string is the invalid name. *)
exception InvalidName of string
exception AmbiguousSubst of Context.ctx_expr * Context.ctx_expr
exception NotLlambda

(* Indicates a success in search *)
exception Success

type case =
  { vars_case : (Term.id * Term.term) list
  ; ctxvars_case : Context.CtxVarCtx.t
  ; hyps_case : Sequent.hyp list
  ; goal_case : Formula.formula
  ; count_case : int
  ; name_case : string
  ; next_subgoal_id_case : int
  ; bind_state_case : Term.bind_state
  }

let make_case seq =
  { vars_case = seq.vars
  ; ctxvars_case = Context.CtxVarCtx.copy seq.ctxvars
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
    name, ([], Context.CtxTy (snd binding, []))
  in
  let new_vars = List.map aux bindings in
  let new_form =
    Formula.replace_ctx_vars
      (List.map2 (fun (bn, _) (nn, _) -> bn, Context.Var nn) bindings new_vars)
      form
  in
  let mapping = List.combine (List.map fst bindings) (List.map fst new_vars) in
  mapping, new_vars, new_form
;;

(* Checks if two context formulas can be made equivalent. [g_seq] is the context
   expression that is universally quantified throughout. [g_form] can be
   existentially quantified. If it is a logical variable, check if we may
   instantiate it with some context expression to make it equivalent to [g].

   If we may instantiate [g_form] with some expression to make it an instance of
   [g_seq], then return the substitution which performs that operation. If
   [g_form] cannot be made into an instance of [g_seq] then return [None]

   This method assumes that the permutation to the nominals has been applied to
   the expressions and their related association lists prior - and therefore
   does not consider them.
*)
let context_instance
  (schemas : (Context.ctx_var, Context.block_schema list) Hashtbl.t)
  (compat : (id * id list) list)
  (nvars : (id * term) list)
  (ctxvar_ctx_seq : Context.CtxVarCtx.t)
  (ctxvar_ctx_form : Context.CtxVarCtx.t)
  (g_form : Context.ctx_expr)
  (g_seq : Context.ctx_expr)
  : (Context.ctx_var * Context.ctx_expr) list option
  =
  let can_instantiate_to_var v_form v_seq =
    (* ensure v_form logical *)
    if Context.CtxVarCtx.mem ctxvar_ctx_form v_form
    then (
      let schema_seq_name = Context.CtxVarCtx.get_var_schema ctxvar_ctx_seq v_seq in
      let schema_seq_name = Option.default "" schema_seq_name in
      let compatible_schemas = List.assoc_opt v_form compat in
      Option.map_default (List.mem schema_seq_name) false compatible_schemas)
    else false
  in
  let can_instantiate_to_expr v_form g_seq =
    match Context.CtxVarCtx.get_var_schema ctxvar_ctx_form v_form with
    | None ->
      (* v_form is universally quantified, but maybe could be extended to
         include more instances of the schema if we retroactively weaken the
         formulas which first instantiated the context variable. *)
      false
    | Some schema_form_name ->
      let schema_form = Hashtbl.find schemas schema_form_name in
      Typing.of_schema nvars ctxvar_ctx_seq g_seq (schema_form_name, schema_form)
  in
  let rec aux g_form g_seq =
    match g_form, g_seq with
    | Context.Nil, Context.Nil -> Some []
    | Context.Var v_form, Context.Var v_seq when v_form = v_seq -> Some []
    | Context.Var v_form, Context.Var v_seq ->
      if can_instantiate_to_var v_form v_seq
      then Some [ v_form, Context.Var v_seq ]
      else None
    | Context.Var v_form, g_seq ->
      (* See if we can instantiate v_form to g_seq *)
      if can_instantiate_to_expr v_form g_seq then Some [ v_form, g_seq ] else None
    | Context.Ctx (g1', (n1, ty1)), Context.Ctx (g2', (n2, ty2)) ->
      if n1 = n2
      then if Unify.try_right_unify ~used:nvars ty1 ty2 then aux g1' g2' else None
      else None
    | _, _ -> None
  in
  aux g_form g_seq
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
let formula_instance schemas compat nvars ctxvar_ctx bound_ctxvars f1 f2 =
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
      else if List.for_all2 (fun (_, s1) (_, s2) -> s1 = s2) bndrs1 bndrs2
      then (
        let subst =
          List.map2 (fun (id1, _) (id2, _) -> id1, Context.Var id2) bndrs1 bndrs2
        in
        let f = Formula.replace_ctx_vars subst f1' in
        let* s = inst f f2' in
        return (subst @ s))
      else None
    | Formula.All (vs1, f1'), Formula.All (vs2, f2')
    | Formula.Exists (vs1, f1'), Formula.Exists (vs2, f2') ->
      if List.length vs1 != List.length vs2
      then None
      else if List.for_all2 (fun idty1 idty2 -> idty1 = idty2) vs1 vs2
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
      then context_instance schemas compat nvars ctxvar_ctx bound_ctxvars g1 g2
      else None
    | Formula.Prop (p1, argtms1), Formula.Prop (p2, argtms2) ->
      if p1 = p2 && List.for_all2 (Unify.try_right_unify ~used:nvars) argtms1 argtms2
      then Some []
      else None
    | _ -> None
  in
  inst f1 f2
;;

(** [generate_partial_mapping f1 f2 res ctxvar_ctxs] will return
    a substitution that represents part of the 1-1 mapping which is forced to be
    held if the explicit portions of [f1] and [f2]'s contexts are to match.

    @param f1 is the universally quantified formula, i.e. from the sequent

    @param f2
      could be either universally or existentially quantified depending
      on if it occurs under some bindings.

    @param res
      is the restricted set which represents which nominal constants
      may be mapped to another in the restricted set.

    @param ctxvar_ctxs the sequent and formula's ctx variable context. *)
let generate_partial_mapping f1 f2 res =
  (* We'll check this in order to fail before we traverse the context and
     generate all possible mappings *)
  let ctx_var_compatible g1 g2 =
    match Context.get_ctx_var_opt g1, Context.get_ctx_var_opt g2 with
    (* Both have context variables, leave schema checking up to subordination *)
    | Some _, Some _ -> true
    (* The universally quantified formula cannot match if it has an implicit
       portion while the existentially quantified formula doesn't.*)
    | Some _, None -> false
    | None, _ -> true
  in
  let not_in_mapping n1 n2 l =
    (not (List.mem n1 (List.map fst l)))
    && not (List.mem (Term.var_to_term n2) (List.map snd l))
  in
  (* Generate a mapping for nominals which we know must hold in order for the
     two context expressions to match. *)
  let rec aux acc g1 g2 =
    match g1, g2 with
    | Context.Ctx (g1', (n1, _)), Context.Ctx (g2', (n2, _)) ->
      if n1 = n2 || (VarSet.mem res n1 && VarSet.mem res n2)
      then
        if not_in_mapping n1 n2 acc
        then aux ((n1, Term.var_to_term n2) :: acc) g1' g2'
        else aux acc g1' g2'
      else aux acc g1' g2'
    | _, (Context.Nil | Context.Var _) -> acc
    | (Context.Nil | Context.Var _), _ -> raise (Unify.UnifyFailure Unify.Generic)
  in
  match f1, f2 with
  | Formula.Atm (g1, _, _, _), Formula.Atm (g2, _, _, _) ->
    if ctx_var_compatible g1 g2
    then aux [] g1 g2
    else
      raise (Unify.UnifyFailure (Unify.ContextFail "could not match context variables"))
  | _ -> []
;;

(* [generate_mappings_for ctxvar_ctx nvars dest_form ?rng src_form] gives
   all possible mappings from [src_form] to [dest_form] which is restricted to
   nominal constants in the relevant set (N gamma or N) *)
let generate_mappings_for ctxvar_ctx nvars dest_form ?rng src_form =
  (* We exclude names from context variable blocks in the mappings as these are
     maintained across the sequent and so cannot be renamed within a formula *)
  (* We limit the mapping's support set to the restricted set of the context
     variable if the ground term has one, otherwise it's all nominals in the
     sequent *)
  let restricted_set =
    match Formula.get_ctx_var_opt src_form with
    | Some g_var -> Option.get (Context.CtxVarCtx.get_var_restricted ctxvar_ctx g_var)
    | None -> VarSet.from_list (List.map (fun (_, x) -> Term.term_to_var x) nvars)
  in
  (* Generate a partial mapping between the explicit portion of the formulas
     contexts. *)
  let forced_mapping = generate_partial_mapping src_form dest_form restricted_set in
  (* Remove any nominals from the domain of the mapping if they are not in
     restricted set *)
  let dom =
    Formula.formula_support_sans ctxvar_ctx src_form
    |> List.filter (fun x -> VarSet.mem restricted_set (Term.term_to_var x))
  in
  (* Get all nominal constants which we are allowed to generate a mapping to *)
  let rng = Option.default (Formula.formula_support_sans ctxvar_ctx dest_form) rng in
  let rng = List.filter (fun x -> VarSet.mem restricted_set (Term.term_to_var x)) rng in
  (* Allow the identity mapping for any term in the ground formula *)
  let rng = rng @ dom |> List.unique in
  (* Remove any items which have already been assigned a mapping in the partial
     permutation. *)
  let rng = List.minus rng (List.map snd forced_mapping) in
  let dom = List.minus dom (List.map (fun (v, _) -> Term.var_to_term v) forced_mapping) in
  let dom_names = List.map term_to_name dom in
  let forced_mapping_subst = List.map (fun (v, t) -> v.Term.name, t) forced_mapping in
  Seq.permute (List.length dom) (List.to_seq rng)
  |> Seq.map (fun subst ->
    List.combine dom_names (List.of_seq subst) @ forced_mapping_subst)
;;

(* Try to unify t1 and t2 under permutations of nominal constants.
   For each successful unification, call sc.
   t1 may contain logic variables, t2 is ground *)
let all_meta_right_permute_unify
  ~sc
  (schemas : (Context.ctx_var, Context.block_schema list) Hashtbl.t)
  compat
  (nvars : (Term.id * Term.term) list)
  (ctxvar_ctx : Context.CtxVarCtx.t)
  (new_ctxvar_ctx : Context.CtxVarCtx.t)
  (t1 : Formula.formula)
  (t2 : Formula.formula)
  (rng : term list)
  =
  let ctxvar_ctx' = Context.CtxVarCtx.union ctxvar_ctx new_ctxvar_ctx in
  let substs = generate_mappings_for ctxvar_ctx' nvars t1 ~rng t2 in
  let aux alist =
    let ctxvar_ctx' = Context.CtxVarCtx.copy ctxvar_ctx in
    Context.CtxVarCtx.map_inplace
      (fun _ (r, b) -> r, Context.replace_ctx_typ_vars alist b)
      ctxvar_ctx';
    try
      let subst =
        formula_instance
          schemas
          compat
          nvars
          ctxvar_ctx'
          new_ctxvar_ctx
          t1
          (Formula.replace_formula_vars alist t2)
      in
      if Option.is_some subst then sc (subst, Term.get_bind_state ())
    with
    | Unify.UnifyFailure _ -> ()
  in
  Seq.iter (Term.unwind_state aux) substs
;;

(* Determines if two formulas are equal up to permutation of nominal constants *)
let permute_eq ~sc nvars ctxvar_ctx f1 f2 =
  let aux subst =
    let f2 = Formula.replace_formula_vars subst f2 in
    if Formula.eq f2 f1 then sc ()
  in
  try
    let support_f1 = Formula.formula_support_sans ctxvar_ctx f1 in
    let support_f2 = Formula.formula_support_sans ctxvar_ctx f2 in
    if List.length support_f1 = List.length support_f2
    then (
      let substs = generate_mappings_for ctxvar_ctx nvars f1 f2 in
      Seq.iter aux substs)
  with
  | Unify.UnifyFailure _ -> ()
;;

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
  | Formula.(LT i, LT j | LT i, EQ j | EQ i, EQ j) when i = j -> true
  | _, Formula.LT _ -> false
  | _, Formula.EQ _ -> false
  | _ -> true
;;

let decompose_app_form g ann args bndrs body =
  let rec mk_fm args bndrs =
    match args, bndrs with
    | [], [] -> []
    | [ arg ], bndrs when List.length bndrs > 1 ->
      [ Formula.Atm (g, arg, pi bndrs body, ann) ]
    | arg :: args', (v, ty) :: bndrs' ->
      Formula.Atm (g, arg, ty, ann)
      :: mk_fm
           args'
           (List.map (fun (b, ty) -> b, Term.replace_term_vars [ v.name, arg ] ty) bndrs')
    | [], _ | _, [] -> bugf "Expected to have same number of args as binders"
  in
  mk_fm args bndrs
;;

let extract_ty_info signature sequent depth formulas =
  (* Find a type with applications in the type.
     Look up the head of that type in the signature.
     Create judgements for the arguments to the type in the assumption
     set to the types they are assigned in the signature. *)
  let extract_tys_from_ty (f : Formula.formula) =
    match f with
    | Formula.(Top | Bottom | Ctx _ | All _ | Exists _ | Imp _ | And _ | Or _ | Prop _) ->
      []
    | Formula.Atm (ctx, _, ty, _) ->
      (match observe (hnorm ty) with
       | App (head, _) when is_var Constant (observe (hnorm head)) ->
         decompose_kinding signature [] ctx ty
       | App _ | Var _ | DB _ | Lam _ | Susp _ | Ptr _ | Pi _ | Type -> [])
  in
  let extract_tys_from_tm (f : Formula.formula) =
    let decompose_app g ann args tm =
      match observe (Term.hnorm tm) with
      | Term.Pi (bndrs, body) -> decompose_app_form g ann args bndrs body
      | App _ | Var _ | DB _ | Lam _ | Susp _ | Ptr _ | Type -> []
    in
    match f with
    | Formula.(Top | Bottom | Ctx _ | All _ | Exists _ | Imp _ | And _ | Or _ | Prop _) ->
      []
    | Formula.Atm (g, m, _, a) ->
      (match observe (hnorm m) with
       | App (h, args) ->
         (match observe (hnorm h) with
          | Term.Var v when v.tag = Term.Constant ->
            (try
               (Signature.lookup_obj_decl signature v.name).Signature.typ
               |> decompose_app g a args
             with
             | Not_found -> raise Success)
          | Term.Var v when v.tag = Term.Nominal ->
            List.assoc v (Context.ctxexpr_to_ctx sequent.ctxvars g)
            |> decompose_app g a args
          | _ -> [])
       | Var _ | DB _ | Lam _ | Susp _ | Ptr _ | Pi _ | Type -> [])
  in
  let rec aux depth formulas =
    if depth <= 0
    then formulas
    else (
      let new_formulas =
        formulas
        |> List.flatten_map (fun f -> f :: extract_tys_from_tm f)
        |> List.flatten_map (fun f -> f :: extract_tys_from_ty f)
        |> List.unique ~cmp:Formula.eq
      in
      (* Stop early if we haven't extracted any new information *)
      if List.length new_formulas = List.length formulas
      then new_formulas
      else aux (depth - 1) new_formulas)
  in
  aux depth formulas
;;

(** Search:
    assumption is that the current goal formula is atomic, or a defined
    proposition.
    raises Success exception if current goal is determined valid by search.

    procedure:
    {ol
     {- once at outset check the nominal constants in explicit part of context
       {ul
        {- no duplicate binding for name }
        {- all explicit bindings must be restricted from appearing in context
          variables
          {ol
           {- Extract all typing information from all hypotheses and add them to the
             assumption set
          }
           {- Then being the search loop attempting to complete derivation
             + normalize the goal formula (i.e. apply Pi-R rule)
             + check for match in assumption set (i.e. apply id rule)
             + decompose typing judgement (i.e. apply atm-R rule)
          }
          }
       }
       }
    }
     {- for leaves perform check of context formation
       must either be the prefix of some context expression from an assumption or
       shown well-formed explicitly
    }
    } *)
let search ~depth signature sequent =
  (* checks that the explicit bindings in context expression g are all distinct and are
     restricted from appearing in any instance of any context variable appearing in g. *)
  let check_context_names g =
    let explicit_names = List.map fst (Context.get_explicit g) in
    List.is_unique explicit_names
    &&
    if Context.has_var g
    then
      List.for_all
        (fun x ->
          let s =
            Context.get_ctx_var g
            |> Context.CtxVarCtx.get_var_restricted sequent.ctxvars
            |> Option.default VarSet.empty
          in
          VarSet.mem s x)
        explicit_names
    else true
  in
  let cvar_to_block_formulas cvar : Formula.formula list =
    let block_to_formulas (block : Context.block) : Formula.formula list =
      List.map (fun (v, t) -> Formula.atm (Context.Var cvar) (Term.var_to_term v) t) block
    in
    let blocks = Context.CtxVarCtx.get_var_blocks sequent.ctxvars cvar in
    List.flatten_map block_to_formulas blocks
  in
  let ctx_formulas =
    List.flatten_map cvar_to_block_formulas (Context.CtxVarCtx.get_vars sequent.ctxvars)
  in
  let formulas =
    List.map (fun hyp -> hyp.formula) sequent.hyps
    |> List.append ctx_formulas
    |> List.unique ~cmp:Formula.eq
    |> extract_ty_info signature sequent depth
  in
  (* aux function does the meat of this function, searching for derivations of each subgoal in list. *)
  let rec search_aux (subgoals : (unit -> unit) list) =
    (* checks that the context g will be a well-formed LF context for any instance of the sequent.
       Note that whenever this function is called we already have checked the names used for
       explicit bindings, so this check is focused on the formation of the LF types in a context expression. *)
    let rec check_context used g =
      let hyp_ctxexprs =
        List.filter_map (fun hyp -> Formula.get_formula_ctx_opt hyp.formula) sequent.hyps
      in
      let support_g = Formula.context_support_sans sequent.ctxvars g in
      (* first, attempts to find an assumption formula with g as a prefix of the context expression. *)
      let match_with_ctx hyp_g =
        if Context.has_var g = Context.has_var hyp_g
        then (
          let support_hypg = Formula.context_support_sans sequent.ctxvars hyp_g in
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
    let try_match () =
      let nvars = Sequent.get_nominals sequent in
      let try_eq f =
        permute_eq ~sc:(fun _ -> raise Success) nvars sequent.ctxvars sequent.goal f
      in
      let match_form f =
        (* try each permutation of nominals in assumption formula *)
        match f with
        | Formula.Atm (_, _, _, ann)
          when satisfies ann (Formula.formula_to_annotation sequent.goal) -> try_eq f
        | Formula.Prop _ -> try_eq f
        | _ -> ()
      in
      List.iter match_form formulas
    in
    (* use atm-R to make a reasoning step. *)
    let lf_step () =
      (* function for constructing the subgoals which might be generated by this step. *)
      let make_subgoals g ann args bndrs body =
        decompose_app_form g ann args bndrs body
        |> List.map (fun f () -> sequent.goal <- f)
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
            List.assoc v (Context.ctxexpr_to_ctx sequent.ctxvars g)
            |> Term.hnorm
            |> freshen_type ~used:sequent.vars ~support:[]
          | Term.Var _ -> bugf "Expected constant or nominal"
          | _ -> bugf "Head of term expected to be a variable"
        in
        (try
           if Term.eq hd_ty a
           then
             check_context
               (Formula.get_formula_used_nominals sequent.ctxvars sequent.goal)
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
            List.assoc v (Context.ctxexpr_to_ctx sequent.ctxvars g)
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

let ind sequent i n =
  let rec mk_ih form i =
    match form with
    | Formula.Imp (l, r) when i = 1 ->
      let aux f =
        match f with
        | Formula.Atm (g, m, a, ann) ->
          if ann = Formula.None
          then
            ( Formula.Imp (Formula.Atm (g, m, a, Formula.LT n), r)
            , Formula.Imp (Formula.Atm (g, m, a, Formula.EQ n), r) )
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
   occurrence in G1,...,Gj and avoid raising these variables because
   such dependencies would be ill-formed. *)
let addBlock
  (seq : Sequent.sequent)
  (tycvar : Context.CtxVarCtx.entry)
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
  let blocks = Context.CtxVarCtx.get_blocks tycvar in
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
  let s = Sequent.cp_sequent seq in
  List.iter (Sequent.add_var s) (List.map Term.term_to_pair new_names);
  List.iter (Sequent.add_var s) psij';
  Sequent.replace_seq_vars thetaj' s;
  List.iter (Sequent.add_var s) (List.map Term.term_to_pair psij'');
  let ctx_id = Context.CtxVarCtx.get_id tycvar in
  let schema = Option.get (Context.CtxVarCtx.get_var_schema s.ctxvars ctx_id) in
  let blocks = Context.CtxVarCtx.get_var_blocks s.ctxvars ctx_id in
  Sequent.remove_ctxvar s ctx_id;
  Context.CtxVarCtx.add_var
    s.ctxvars
    ctx_id
    ~res:(Context.CtxVarCtx.get_restricted tycvar |> VarSet.to_list)
    (Context.CtxTy (schema, List.take j blocks @ [ g ] @ List.drop j blocks));
  (* returning heads tuple *)
  let ni, ai = List.nth g i in
  s, Term.var_to_term ni, ai
;;

(* enumerates all the name choices of arity types atys relative to
   names and away from prohibited.
*)
let rec namesLists (atys : Type.ty list) (names : VarSet.t) (prohibited : VarSet.t)
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
           (List.map
              (fun v -> Term.term_to_pair (Term.var_to_term v))
              VarSet.(union names prohibited |> to_list)))
    in
    let avail_choices =
      VarSet.minus names prohibited
      |> VarSet.filter (fun v -> v.ty = a)
      |> VarSet.to_list
      |> List.map Term.var_to_term
    in
    let pick n =
      namesLists atys' names (VarSet.add_var prohibited (Term.term_to_var n))
      |> List.map (fun l -> n :: l)
    in
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
  (tycvar : Context.CtxVarCtx.entry)
  (bl_schm : Context.block_schema)
  : (Sequent.sequent * Term.term * Term.term) list
  =
  let (Context.B (_, entries)) = bl_schm in
  let entry_atys = List.map (fun (v, _) -> v.ty) entries in
  let noms =
    Sequent.get_nominals seq
    |> List.map (fun (_, s) -> Term.term_to_var s)
    |> VarSet.from_list
  in
  let n_gamma = Context.CtxVarCtx.get_restricted tycvar in
  let prohibited =
    Context.ctxexpr_to_ctx seq.ctxvars g |> List.map fst |> VarSet.from_list
  in
  let usable = VarSet.minus (VarSet.minus noms n_gamma) prohibited in
  (* for each location in the block list j
     0 to
     (let CtxTy(schema, blocks) = Sequent.get_ctxvar_ty tycvar in
     List.length blocks)
     for every list of names in namelsts names,
     for every binding in the block i
     1 to (List.length entries),
     call:
     addblock seq tycvar bl_schm names usable j i *)
  let namelsts = namesLists entry_atys usable (VarSet.union n_gamma prohibited) in
  let blocks = Context.CtxVarCtx.get_blocks tycvar in
  let js = List.range 0 (List.length blocks) in
  let is = List.range 0 (List.length entries - 1) in
  List.flatten_map
    (fun j ->
      List.flatten_map
        (fun names ->
          List.map
            (fun i ->
              addBlock
                seq
                tycvar
                bl_schm
                names
                (List.minus (VarSet.to_term_list usable) names)
                j
                i)
            is)
        namelsts)
    js
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
       U{allBlocks seq g tycvar bl_schemai | 1<= i<= m}
   where
   - tycvar = Gamma|NGamma:C[G1,...,Gn]
*)
let implicitHeads seq schemas (g : Context.ctx_expr)
  : (Sequent.sequent * Term.term * Term.term) list
  =
  let gamma = Context.get_ctx_var g in
  let tycvar = Context.CtxVarCtx.find seq.ctxvars gamma in
  let tycvar = gamma, tycvar in
  let schema = Context.CtxVarCtx.get_schema tycvar in
  let block_schemas = Hashtbl.find schemas schema in
  List.flatten_map (allBlocks seq g tycvar) block_schemas
;;

(* returns the tuple (seq, n:A) for each explicit binding in g
   relative to seq.*)
let explicitHeads seq g : (Sequent.sequent * Term.term * Term.term) list =
  let explicit_bnds = Context.ctxexpr_to_ctx seq.ctxvars g in
  List.map (fun (h, ty) -> seq, Term.var_to_term h, ty) explicit_bnds
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
   expression g relative to seq. *)
let heads lf_sig schemas seq g =
  let sig_heads = sigHeads lf_sig seq in
  let ex_heads = explicitHeads seq g in
  if Context.has_var g
  then sig_heads @ ex_heads @ implicitHeads seq schemas g
  else sig_heads @ ex_heads
;;

(* generates and adds cases for the head h:typ
   Assumes that the given formula atomic formula and that it actually
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
       Formula.get_formula_used seq.ctxvars form
       @ Formula.get_formula_used_nominals seq.ctxvars form
       |> List.iter (fun (_, t) -> Sequent.add_var seq (term_to_pair t));
       let new_hyps =
         List.map2
           (fun t ty -> Formula.Atm (g, t, ty, Formula.reduce_inductive_annotation ann))
           new_tms
           new_lftys
       in
       List.iter (Sequent.add_hyp seq) new_hyps;
       let newGoal = Formula.eta_expand seq.goal in
       seq.goal <- newGoal;
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
      let _ = Signature.lookup_type_decl lf_sig v.name in
      v.name
    | App (h, _) ->
      (match Term.norm h with
       | Var v when v.tag = Constant ->
         let _ = Signature.lookup_type_decl lf_sig v.name in
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
    |> List.map (fun (g, t, ty) -> g, Term.eta_expand t, Term.eta_expand ty)
  in
  let per_head (seq, h, typ) =
    (* let (save_seq,bind_state) = (Sequent.cp_sequent seq, Term.get_bind_state ()) in *)
    let hyp = get_hyp seq id in
    let case = makeCases hyp.Sequent.formula seq h typ in
    (* let _ = Sequent.assign_sequent seq save_seq; *)
    (*         Term.set_bind_state bind_state in *)
    case
  in
  List.flatten_map per_head case_heads
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
      sequent.goal <-
        Formula.replace_formula_vars_rename
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
      (let diff = Int.compare (List.length formal) (List.length actual) in
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

(* Normalizes [form] by removing pi abstractions until it is an atomic typing
   judgement. Each pi binding is replaced by a new nominal variable wrt [nvars],
   but this nominal is not added to the sequent's variables - as a permutation
   must map to it. After this permutation the variable will be removed via this
   operation happening in another derivation of the =>L rule.

   Returns the normalized formula and the nominals that were added to the
   context via removing the pi abstractions. This list is in reverse order -
   where the first element is the last nominal in the context. *)
let normalize_atomic_formula nvars form =
  let nvars = ref nvars in
  let rec aux (form : Formula.formula) added =
    match form with
    | Formula.Atm (g, m, a, ann) ->
      (match Term.observe (Term.hnorm a) with
       | Term.Pi ((v, typ) :: bndrs, body) ->
         (* for each binder introduce new name n, raise relevant eigenvariables over n,
            then move into context and apply term component to this n. *)
         let name, _ = Term.fresh_wrt ~ts:2 Nominal "n" v.Term.ty !nvars in
         let _ = nvars := Term.term_to_pair name :: !nvars in
         let g' = Context.Ctx (g, (Term.term_to_var name, typ)) in
         let m' = Term.app m [ Term.eta_expand name ] in
         let a' =
           Term.replace_term_vars
             [ v.Term.name, Term.eta_expand name ]
             (Term.pi bndrs body)
         in
         aux (Formula.atm ~ann g' m' a') (name :: added)
       | _ -> form, added)
    | _ -> form, added
  in
  aux form []
;;

(* Given some formula [f] and the nominals that replace the pi abstractions in another
   formula, generate a substitution for the formula's explicit portion which is restricted
   to these nominals - otherwise raise a unify failure. *)
let generate_subst f added ctx_var_ctx =
  let is_valid_perm g added alist ctx_var_ctx =
    (* All variables in the substitution must be in the restricted set *)
    let restriction_check vars r = List.for_all (fun v -> VarSet.mem r v) vars in
    let unique_check l =
      let src = List.map fst l in
      let dst = List.map snd l in
      List.length src = List.length (List.unique src)
      && List.length dst = List.length (List.unique dst)
    in
    let only_restricted =
      if Context.has_var g
      then
        restriction_check
          (List.map fst alist)
          (Option.get
             (Context.CtxVarCtx.get_var_restricted ctx_var_ctx (Context.get_ctx_var g)))
      else true
    in
    let all_mapped = List.length added = List.length alist in
    let all_unique = unique_check alist in
    only_restricted && all_unique && all_mapped
  in
  let types_valid ctx_entries =
    List.fold_left
      (fun used_vars (v, tm) ->
        let tms = Term.find_vars Nominal [ tm ] in
        if List.exists (fun tm_var -> List.mem tm_var used_vars) tms
        then raise (Unify.UnifyFailure Unify.Generic)
        else v :: used_vars)
      []
      ctx_entries
  in
  match f with
  | Formula.Atm (g, _, _, _) ->
    let ctx = Context.get_explicit g in
    let ctx_vars = List.map fst ctx in
    let perm = List.combine_shortest ctx_vars added |> List.rev in
    let _ = types_valid ctx in
    if is_valid_perm g added perm ctx_var_ctx
    then perm
    else raise (Unify.UnifyFailure Unify.Generic)
  | _ -> []
;;

let apply_arrow
  schemas
  compat
  nvars
  (ctxvar_ctx : Context.CtxVarCtx.t)
  (bound_ctxvars : Context.CtxVarCtx.t)
  form
  args
  =
  (* Determines if there are two possible distinct context substitutions that
     can be made. If there is some ambiguity, reject the application in case the
     ambiguity may unnecessarily reject some application *)
  let set_res_or_raise res new_res =
    let can_be_ambiguous subst =
      let _, expr = subst in
      Context.length expr > 1
    in
    let get_differing_permutation
      (subst1 : ctx_subst list option)
      (subst2 : ctx_subst list option)
      : (ctx_subst * ctx_subst) option
      =
      let sort_by_ctx_var substs =
        List.sort (fun (v1, _) (v2, _) -> String.compare v1 v2) substs
      in
      match subst1, subst2 with
      | None, _ | _, None -> None
      | Some subst1, Some subst2 ->
        let norm_subst1 = List.filter can_be_ambiguous subst1 |> sort_by_ctx_var in
        let norm_subst2 = List.filter can_be_ambiguous subst2 |> sort_by_ctx_var in
        List.combine_shortest norm_subst1 norm_subst2
        |> List.find_opt (fun ((v1, d1), (v2, d2)) ->
          Context.ctx_var_eq v1 v2 && not (Context.eq d1 d2))
    in
    if Option.is_none (fst !res) then res := new_res;
    if List.exists can_be_ambiguous (Option.default [] (fst !res))
    then (
      let subst1, _ = !res in
      let subst2, _ = new_res in
      match get_differing_permutation subst1 subst2 with
      | None -> ()
      | Some (s1, s2) ->
        let ctx1 = snd s1 in
        let ctx2 = snd s2 in
        raise (AmbiguousSubst (ctx1, ctx2)))
    else raise Success
  in
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
            | _ -> normalize_atomic_formula nvars f
          in
          let support_antecedent =
            Formula.formula_support_sans
              (Context.CtxVarCtx.union ctxvar_ctx bound_ctxvars)
              left
          in
          let left, added = norm left in
          let subst = generate_subst arg added ctxvar_ctx in
          let arg =
            Formula.replace_formula_vars
              (List.map (fun (v, t) -> v.Term.name, t) subst)
              arg
          in
          (* check if left has annotation & ensure arg
             can satisfy it *)
          if satisfies
               (Formula.formula_to_annotation arg)
               (Formula.formula_to_annotation left)
          then (
            try
              all_meta_right_permute_unify
                ~sc:(set_res_or_raise res)
                schemas
                compat
                nvars
                ctxvar_ctx
                bound_ctxvars
                left
                arg
                support_antecedent
            with
            | Success -> ());
          (match !res with
           | Some ctx_subst, bind_state ->
             Term.set_bind_state bind_state;
             Formula.replace_ctx_vars ctx_subst right
           | None, _ -> raise (Unify.UnifyFailure (Unify.MatchingFormula arg)))
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
let apply schemas ~sub_rel sequent formula args =
  let process_bindings ctxs compatible_schemas foralls body =
    let mapping, new_ctxvars, body' =
      freshen_ctx_bindings
        (Context.CtxVarCtx.map_entries Context.CtxVarCtx.get_id sequent.ctxvars)
        ctxs
        body
    in
    let fresh_compat =
      List.map (fun (src, dest) -> dest, List.assoc src compatible_schemas) mapping
      |> List.filter (fun (src, _) -> Formula.occurs_negatively src body')
    in
    let nvars = List.filter (fun (_, t) -> is_var Nominal t) sequent.vars in
    apply_arrow
      schemas
      fresh_compat
      nvars
      sequent.ctxvars
      (Context.CtxVarCtx.of_list_list new_ctxvars)
      (freshen_nameless_bindings ~support:(List.map snd nvars) ~ts:1 foralls body')
      args
  in
  let collect_bindings formula =
    let rec aux ctxbndrs varbndrs formula =
      match Formula.norm formula with
      | Formula.Ctx (bndrs, body) -> aux (ctxbndrs @ bndrs) varbndrs body
      | Formula.All (vs, body) -> aux ctxbndrs (varbndrs @ vs) body
      | Formula.Imp (_, _) -> ctxbndrs, varbndrs, formula
      | _ ->
        [ "Structure of applied term must be a substructure of the following."
        ; "<ctx/forall quantifiers> F1 => ... => Fk => F"
        ]
        |> String.concat "\n"
        |> failwith
    in
    aux [] [] formula
  in
  let ctxbndrs, varbndrs, body = collect_bindings formula in
  let compat =
    Formula.get_compatible_context_schemas (Hashtbl.to_list schemas) sub_rel formula
  in
  process_bindings ctxbndrs compat varbndrs body
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

let apply_with ?schemas ~sub_rel sequent formula args (vwiths, cwiths) =
  let schemas =
    Option.default
      (Hashtbl.create 1
       |> fun h ->
       Hashtbl.add h Context.empty_schema_name [];
       h)
      schemas
  in
  (* let formula = Formula.lift_empty_ctx formula in *)
  if args = [] && vwiths = [] && cwiths = []
  then formula
  else (
    let term = instantiate_withs formula (vwiths, cwiths) in
    apply schemas ~sub_rel sequent (Formula.norm term) args)
;;

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
    sequent.goal <-
      Formula.replace_formula_vars
        (List.map2 (fun (n, _) (_, t) -> n, Term.app t support) vs new_vars)
        f
  | Formula.Ctx (cvars, f) ->
    let cvars_alist, _ =
      Context.list_fresh_wrt cvars (Context.CtxVarCtx.get_vars sequent.ctxvars)
    in
    let cvars' = List.map (fun (_, v', t) -> v', t) cvars_alist in
    let alist = List.map (fun (v, v', _) -> v, Context.Var v') cvars_alist in
    let cvars' =
      List.map (fun (v, id) -> v, (ref VarSet.empty, Context.ctx_typ ~id ())) cvars'
    in
    Context.CtxVarCtx.add_vars sequent.ctxvars cvars';
    sequent.goal <- Formula.replace_ctx_vars alist f
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

type permutation_failure =
  | IncompletePermutation of Term.id list
  | MultiMappedPermutation of Term.id list
  | OutOfResSetPermutation of Term.id list

exception PermutationFailure of permutation_failure

let permute_ctx form g' =
  (* need to verify that
     (1) all items in g are in g' and all in g ' are in g
     (2) g' respects dependencies (i.e. no name is used
     in a type before it appears in the context) *)
  let rec check_dependencies = function
    | [], [] -> ()
    | v :: vs, _ :: typs ->
      if List.mem v.Term.name (List.map fst (Term.get_used typs))
      then raise (InvalidCtxPermutation "context items cannot depend on later name");
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
               ("not found: " ^ v.Term.name ^ ". all entries must be in both contexts")))
        else ())
      g'_explicit;
    check_dependencies (List.split g'_explicit);
    Formula.atm ~ann g' m a
  | _ -> bugf "Expected atomic formula when permuting context"
;;

let permute form perm sequent =
  let incomplete_mapped_nominals () =
    let dom = List.map fst perm in
    let rng = List.map snd perm in
    List.remove_all (fun v -> List.mem v rng) dom
    @ List.remove_all (fun v -> List.mem v dom) rng
  in
  let multiple_mapped_nominals () =
    let dom = List.find_duplicates (List.map fst perm) in
    let rng = List.find_duplicates (List.map snd perm) in
    List.unique (dom @ rng)
  in
  let invalid_nominals f =
    match f with
    | Formula.Atm (g, _, _, _) ->
      let perm_supp =
        VarSet.from_list
          (List.map
             (fun (v, _) -> { name = v; tag = Nominal; ts = 2; ty = Type.oty })
             perm)
      in
      let restricted_set =
        match Context.get_ctx_var_opt g with
        | Some g_var ->
          Option.get (Context.CtxVarCtx.get_var_restricted sequent.ctxvars g_var)
        | None ->
          VarSet.from_list
            (List.map (fun (_, x) -> Term.term_to_var x) (Sequent.get_nominals sequent))
      in
      VarSet.minus perm_supp restricted_set |> VarSet.to_id_list
    | _ -> []
  in
  let rec permute' f =
    match f with
    | Formula.Atm _ ->
      (match invalid_nominals f with
       | [] ->
         let form_noms = Formula.get_formula_used_nominals sequent.ctxvars f in
         let alist =
           List.filter (fun (v, _) -> List.mem_assoc v form_noms) perm
           |> List.map (fun (v, _) ->
             let tm = List.assoc v form_noms |> Term.rename_vars perm in
             v, tm)
         in
         Formula.replace_formula_vars alist f
       | noms -> raise (PermutationFailure (OutOfResSetPermutation noms)))
    | Formula.Ctx (bndrs, f) ->
      (* Add all of the bound ctx vars to the ctx var ctx with the entire
         support set of the sequent as its restricted set*)
      let nominals =
        Sequent.get_nominals sequent |> List.map (fun (_, t) -> Term.term_to_var t)
      in
      let cvars_alist, _ =
        Context.list_fresh_wrt bndrs (Context.CtxVarCtx.get_vars sequent.ctxvars)
      in
      let cvars' =
        List.map
          (fun (_, v', id) ->
            v', (ref (VarSet.from_list nominals), Context.ctx_typ ~id ()))
          cvars_alist
      in
      let alist = List.map (fun (v, v', _) -> v, Context.Var v') cvars_alist in
      let alist_rev = List.map (fun (v, v', _) -> v', Context.Var v) cvars_alist in
      Context.CtxVarCtx.add_vars sequent.ctxvars cvars';
      let f' = permute' (Formula.replace_ctx_vars alist f) in
      Context.CtxVarCtx.remove_all (fun v _ -> List.mem_assoc v cvars') sequent.ctxvars;
      let f'' = Formula.replace_ctx_vars alist_rev f' in
      Formula.Ctx (bndrs, f'')
    | Formula.Top -> Formula.Top
    | Formula.Bottom -> Formula.Bottom
    | Formula.Prop (d, t) -> Formula.Prop (d, t)
    (* These binders don't change the permutation and are skipped over *)
    | Formula.All (t, f) -> Formula.All (t, permute' f)
    | Formula.Exists (t, f) -> Formula.Exists (t, permute' f)
    (* propagate the permutation across connectives *)
    | Formula.Imp (l, r) -> Formula.Imp (permute' l, permute' r)
    | Formula.And (l, r) -> Formula.And (permute' l, permute' r)
    | Formula.Or (l, r) -> Formula.Or (permute' l, permute' r)
  in
  match incomplete_mapped_nominals (), multiple_mapped_nominals () with
  | [], [] -> permute' form
  | [], ns -> raise (PermutationFailure (MultiMappedPermutation ns))
  | ns, _ -> raise (PermutationFailure (IncompletePermutation ns))
;;

let strengthen ctxvars form =
  match form with
  | Formula.Atm (Context.Ctx (g, (v, _)), m, a, ann) ->
    let used = Formula.formula_support ctxvars (Formula.Atm (g, m, a, ann)) in
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
    let pristine = State.snapshot () in
    let g1, b, g2 = Context.split_ctx g n in
    let to_prove = Formula.Atm (g1, t, b, Formula.None) in
    (try
       State.reload pristine;
       sequent.Sequent.goal <- to_prove;
       search ~depth lf_sig sequent;
       raise (InstTypeError to_prove)
     with
     | Success ->
       let _ = State.reload pristine in
       let g2' =
         List.map
           (fun (id, ty) -> id, Term.replace_term_vars ~tag:Term.Nominal subst ty)
           g2
         |> List.rev
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
let prune sub_rel sequent form =
  match form with
  | Formula.Atm (g, m, a, _) when Context.has_var g ->
    let hd, args =
      let h = Term.norm m in
      match h with
      | Term.App (hd, args) -> hd, args
      | _ -> bugf "Expected application when pruning"
    in
    let gamma = Context.get_ctx_var g in
    let cvar = gamma, Context.CtxVarCtx.find sequent.ctxvars gamma in
    let bound_names =
      List.map fst (Context.ctxexpr_to_ctx sequent.ctxvars g) |> VarSet.from_list
    in
    let restricted = VarSet.minus (Context.CtxVarCtx.get_restricted cvar) bound_names in
    let (Type.Ty (atys, id)) = Term.get_var_ty hd in
    let ns = List.map Term.eta_normalize args in
    let subordinates =
      Context.get_explicit g
      |> List.map (fun (v, t) ->
        v, Subordination.subordinates sub_rel (Term.get_ty_head t) (Term.get_ty_head a))
    in
    let to_prune =
      List.map
        (fun t ->
          VarSet.mem restricted (Term.term_to_var t)
          || List.assoc_opt (Term.term_to_var t) subordinates = Some false)
        args
    in
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
    Sequent.replace_seq_vars subst sequent
  | Formula.Atm _ -> ()
  | _ -> bugf "Expected pruning atomic formula"
;;
