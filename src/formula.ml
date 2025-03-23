(*
 *
 * FORMULA
 * Representation of the Formulas of the logic.
 *
 *)
open Term
open Context
open Extensions

type annotation =
  | None
  | EQ of int
  | LT of int

type formula =
  | Top
  | Bottom
  | Atm of ctx_expr * term * term * annotation
  | Ctx of (id * id) list * formula
  | All of tyctx * formula
  | Exists of tyctx * formula
  | Imp of formula * formula
  | And of formula * formula
  | Or of formula * formula
  | Prop of id * term list

module Print = struct
  let pr_str ppf s = Format.fprintf ppf "%s" s

  let pr_ann ppf = function
    | None -> ()
    | EQ i -> Format.fprintf ppf "%s" (String.make i '@')
    | LT i -> Format.fprintf ppf "%s" (String.make i '*')
  ;;

  let rec pr_ctxbndrs ppf bndrs =
    match bndrs with
    | [] -> ()
    | (n, schema) :: bndrs' ->
      Format.fprintf ppf "ctx %a@,:@,%a,@ %a" pr_str n pr_str schema pr_ctxbndrs bndrs'
  ;;

  let rec pr_allbndrs ppf bndrs =
    match bndrs with
    | [] -> ()
    | (n, _) :: bndrs' -> Format.fprintf ppf "forall %a,@ %a" pr_str n pr_allbndrs bndrs'
  ;;

  let rec pr_existsbndrs ppf bndrs =
    match bndrs with
    | [] -> ()
    | (n, _) :: bndrs' ->
      Format.fprintf ppf "exists %a,@ %a" pr_str n pr_existsbndrs bndrs'
  ;;

  let rec pr_formula ppf = function
    | Top -> Format.fprintf ppf "%s" "True"
    | Bottom -> Format.fprintf ppf "%s" "False"
    | Atm (g, m, a, ann) when Context.is_empty g ->
      Format.fprintf
        ppf
        "@[<2>{%a@ :@ %a}%a@]"
        (Term.Print.pr_term [])
        m
        (Term.Print.pr_term [])
        a
        pr_ann
        ann
    | Atm (g, m, a, ann) ->
      Format.fprintf
        ppf
        "@[<2>{%a@,@ |-@ @,%a@ :@ %a}%a@]"
        Context.Print.pr_ctxexpr
        g
        (Term.Print.pr_term [])
        m
        (Term.Print.pr_term [])
        a
        pr_ann
        ann
    | Ctx (bndrs, f) -> Format.fprintf ppf "@[<2>%a%a@]" pr_ctxbndrs bndrs pr_formula f
    | All (bndrs, f) -> Format.fprintf ppf "@[<2>%a%a@]" pr_allbndrs bndrs pr_formula f
    | Exists (bndrs, f) ->
      Format.fprintf ppf "@[<2>%a%a@]" pr_existsbndrs bndrs pr_formula f
    | Imp (f1, f2) -> Format.fprintf ppf "@[<4>%a@ =>@ %a@]" pr_formula f1 pr_formula f2
    | And (f1, f2) ->
      Format.fprintf ppf "@[<4>%a@ %a@ %a@]" pr_formula f1 pr_str "/\\" pr_formula f2
    | Or (f1, f2) ->
      Format.fprintf ppf "@[<4>%a@ %a@ %a@]" pr_formula f1 pr_str "\\/" pr_formula f2
    | Prop (h, argtms) -> Format.fprintf ppf "@[<3>%a%a@]" pr_str h pr_propargs argtms

  and pr_typing_judgement ppf = function
    | Atm (g, m, a, ann) ->
      Format.fprintf
        ppf
        "@[<2>%a@,@ |-@ @,%a@ :@ %a%a@]"
        Context.Print.pr_ctxexpr
        g
        (Term.Print.pr_term [])
        m
        (Term.Print.pr_term [])
        a
        pr_ann
        ann
    | f -> pr_formula ppf f

  and pr_propargs ppf = function
    | [] -> ()
    | arg :: args' ->
      Format.fprintf ppf "@ %a%a" (Term.Print.pr_term []) arg pr_propargs args'
  ;;

  let string_of_formula f =
    pr_formula Format.str_formatter f;
    Format.flush_str_formatter ()
  ;;
end

(* Checks if two formulas are equal, ignoring annotations. *)
let rec eq f1 f2 =
  match f1, f2 with
  | Top, Top | Bottom, Bottom -> true
  | Atm (g1, m1, a1, _), Atm (g2, m2, a2, _) ->
    Context.eq g1 g2 && Term.eq m1 m2 && Term.eq a1 a2
  | Ctx (cvars1, f1), Ctx (cvars2, f2) ->
    (try
       List.fold_left2
         (fun acc (cv1, cty1) (cv2, cty2) -> acc && cv1 = cv2 && cty1 = cty2)
         true
         cvars1
         cvars2
       && eq f1 f2
     with
     | Invalid_argument _ -> false)
  | All (vars1, f1), All (vars2, f2) | Exists (vars1, f1), Exists (vars2, f2) ->
    (try
       List.fold_left2
         (fun acc (v1, aty1) (v2, aty2) -> acc && v1 = v2 && Type.eq aty1 aty2)
         true
         vars1
         vars2
       && eq f1 f2
     with
     | Invalid_argument _ -> false)
  | Imp (l1, r1), Imp (l2, r2) | And (l1, r1), And (l2, r2) | Or (l1, r1), Or (l2, r2) ->
    eq l1 l2 && eq r1 r2
  | Prop (p1, args1), Prop (p2, args2) ->
    (try p1 = p2 && List.for_all2 (fun x y -> Term.eq x y) args1 args2 with
     | Invalid_argument _ -> false)
  | _, _ -> false
;;

(* Constructions *)
let atm ?(ann = None) g m a = Atm (g, m, a, ann)
let imp l r = Imp (l, r)
let f_and l r = And (l, r)
let f_or l r = Or (l, r)

let forall vs t =
  if vs = []
  then t
  else (
    match t with
    | All (vs', t') -> All (vs @ vs', t')
    | _ -> All (vs, t))
;;

let exists vs t =
  if vs = []
  then t
  else (
    match t with
    | Exists (vs', t') -> Exists (vs @ vs', t')
    | _ -> Exists (vs, t))
;;

let ctx vs t =
  if vs = []
  then t
  else (
    match t with
    | Ctx (vs', t') -> Ctx (vs @ vs', t')
    | _ -> Ctx (vs, t))
;;

let prop id tms = Prop (id, tms)

(* Manipulations *)

let map_terms f t =
  let rec aux t =
    match t with
    | Atm (g, m, a, ann) -> atm ~ann (context_map f g) (f m) (f a)
    | Imp (a, b) -> imp (aux a) (aux b)
    | All (bindings, body) -> forall bindings (aux body)
    | Exists (bindings, body) -> exists bindings (aux body)
    | Ctx (bindings, body) -> ctx bindings (aux body)
    | Or (a, b) -> f_or (aux a) (aux b)
    | And (a, b) -> f_and (aux a) (aux b)
    | Top | Bottom -> t
    | Prop (p, tmlst) -> prop p (List.map f tmlst)
  in
  aux t
;;

let formula_to_annotation f =
  match f with
  | Atm (_, _, _, r) -> r
  | _ -> None
;;

let reduce_inductive_annotation r =
  match r with
  | EQ i -> LT i
  | _ -> r
;;

let rec collect_vars_ctx = function
  | Top | Bottom | Prop _ -> []
  | Imp (l, r) | Or (l, r) | And (l, r) -> collect_vars_ctx l @ collect_vars_ctx r
  | Atm (g, _, _, _) -> Context.get_explicit g |> List.map fst
  | All (_, f) | Exists (_, f) | Ctx (_, f) -> collect_vars_ctx f
;;

(* Variable Renaming *)
let rec collect_terms ctxvars = function
  | Top | Bottom -> []
  | Imp (l, r) | Or (l, r) | And (l, r) ->
    collect_terms ctxvars l @ collect_terms ctxvars r
  | Atm (g, m, a, _) -> collect_terms_ctx ctxvars g @ [ m; a ]
  | All (_, f) | Exists (_, f) | Ctx (_, f) -> collect_terms ctxvars f
  | Prop (_, tmlst) -> tmlst

and collect_terms_ctx ctxvars = function
  | Nil -> []
  | Context.Var g ->
    let blocks = Context.CtxVarCtx.get_var_blocks ctxvars g in
    List.map snd (List.flatten blocks)
  | Ctx (expr, (_, t)) -> t :: collect_terms_ctx ctxvars expr
;;

let term_support t = Term.find_var_refs Nominal [ t ]
let term_list_support l = Term.find_var_refs Nominal l
let context_support ctxvars c = Context.find_var_refs ctxvars Nominal c

let formula_support ctxvars f =
  let rec aux = function
    | Top | Bottom -> []
    | And (l, r) | Or (l, r) | Imp (l, r) -> aux l @ aux r
    | All (_, f') | Exists (_, f') | Ctx (_, f') -> aux f'
    | Atm (g, m, a, _) -> context_support ctxvars g @ term_support m @ term_support a
    | Prop (_, tmlst) -> term_list_support tmlst
  in
  List.unique ~cmp:Term.eq (aux f)
;;

let get_formula_used_ctxvars f =
  let bound_ctxvars : Context.ctx_var list ref = ref [] in
  let rec ctx_exprs = function
    | Top | Bottom | Prop _ -> []
    | Imp (l, r) | And (l, r) | Or (l, r) -> ctx_exprs l @ ctx_exprs r
    | All (_, f) | Exists (_, f) -> ctx_exprs f
    | Ctx (cvars, f) ->
      bound_ctxvars := List.map fst cvars @ !bound_ctxvars;
      ctx_exprs f
    | Atm (g, _, _, _) -> [ g ]
  in
  let cexprs = ctx_exprs f in
  let used_ctxvars = Context.get_used_ctxvars cexprs in
  List.minus used_ctxvars !bound_ctxvars
;;

let get_formula_ctx_opt f =
  match f with
  | Atm (g, _, _, _) -> Some g
  | _ -> None
;;

let get_ctx_var_opt f =
  let* g = get_formula_ctx_opt f in
  let* ctx = Context.get_ctx_var_opt g in
  return ctx
;;

let formula_support_sans ctxvars f =
  let supp = formula_support ctxvars f in
  get_formula_used_ctxvars f
  |> List.flatten_map (fun v -> context_support ctxvars (Context.Var v))
  |> List.minus supp
;;

let context_support_sans ctxvars g =
  let supp = context_support ctxvars g in
  if Context.has_var g
  then
    List.minus
      supp
      (Context.find_var_refs ctxvars Term.Nominal (Context.Var (Context.get_ctx_var g)))
  else supp
;;

let get_formula_used ctxvars t =
  List.map term_to_pair (Term.find_var_refs Eigen (collect_terms ctxvars t))
;;

let get_formula_used_nominals ctxvars t =
  List.map term_to_pair (formula_support ctxvars t)
;;

let fresh_alist ~used ~tag ~ts tids =
  let used = ref used in
  List.map
    (fun (n, t) ->
      let fresh, curr_used = Term.fresh_wrt ~ts tag n t !used in
      used := curr_used;
      (* (n, Term.eta_expand fresh)) *)
      n, fresh)
    tids
;;

let raise_type support ty =
  let rtys = List.map (tc []) support in
  Type.tyarrow rtys ty
;;

let fresh_raised_alist ~used ~tag ~ts ~support tids =
  let ids, tys = List.split tids in
  let rtys = List.map (raise_type support) tys in
  let alist = fresh_alist ~used ~tag ~ts (List.combine ids rtys) in
  List.map (fun (id, t) -> id, app t support) alist, List.map snd alist
;;

let replace_formula_vars alist t =
  let term_aux alist = replace_term_vars alist in
  let ctx_aux alist = replace_ctx_expr_vars alist in
  let rec aux alist t =
    match t with
    | Top | Bottom -> t
    | Imp (l, r) -> imp (aux alist l) (aux alist r)
    | Or (l, r) -> f_or (aux alist l) (aux alist r)
    | And (l, r) -> f_and (aux alist l) (aux alist r)
    | Atm (g, m, a, ann) ->
      atm ~ann (ctx_aux alist g) (term_aux alist m) (term_aux alist a)
    | All (vs, f) ->
      let alist = List.remove_assocs (List.map fst vs) alist in
      forall vs (aux alist f)
    | Exists (vs, f) ->
      let alist = List.remove_assocs (List.map fst vs) alist in
      exists vs (aux alist f)
    | Ctx (cvars, f) -> ctx cvars (aux alist f)
    | Prop (p, tmlst) -> prop p (List.map (term_aux alist) tmlst)
  in
  aux alist t
;;

(* performs a replacement on formula vars and will rename any quantifiers in the formula
   which appear in the substitution. *)
let rec replace_formula_vars_rename ~used alist t =
  let term_aux alist = replace_term_vars alist in
  let ctx_aux alist = replace_ctx_expr_vars alist in
  let rec rename_sub used fvars = function
    | [] -> used, [], []
    | (id, ty) :: bndrs ->
      let used', bndrs', alist = rename_sub used fvars bndrs in
      if List.mem id fvars
      then (
        (* get a fresh variable to replace this identifier with *)
        let fresh, curr_used = Term.fresh_wrt ~ts:1 Term.Logic id ty used in
        ( used' @ curr_used
        , (Term.get_id fresh, Term.get_var_ty fresh) :: bndrs'
        , (id, fresh) :: alist ))
      else used', (id, ty) :: bndrs', alist
  in
  let rec aux alist t =
    match t with
    | Top | Bottom -> t
    | Imp (l, r) -> imp (aux alist l) (aux alist r)
    | Or (l, r) -> f_or (aux alist l) (aux alist r)
    | And (l, r) -> f_and (aux alist l) (aux alist r)
    | Atm (g, m, a, ann) ->
      atm ~ann (ctx_aux alist g) (term_aux alist m) (term_aux alist a)
    | All (vs, f) ->
      let alist = List.remove_assocs (List.map fst vs) alist in
      let subst_free =
        List.map Term.get_id (Term.find_var_refs Term.Eigen (List.map snd alist))
      in
      (* if any of the free variables in the substitution appear in vs *)
      (* then need to first replace the quantified variable with a new *)
      (* name then proceed with the substitution. *)
      (* we will walk through vs producing vs' and a substitution. if *)
      (* at the end the substitution is empty then no names will be *)
      (* captured, otherwise apply the renaming substituion first then *)
      (* the current substitution can proceed. *)
      let used', vs', alist' = rename_sub used subst_free vs in
      (match alist' with
       | [] -> forall vs (aux alist f)
       | _ ->
         let f' = replace_formula_vars_rename ~used:used' alist' f in
         forall vs' (aux alist f'))
    | Exists (vs, f) ->
      let alist = List.remove_assocs (List.map fst vs) alist in
      let subst_free =
        List.map Term.get_id (Term.find_var_refs Term.Eigen (List.map snd alist))
      in
      let used', vs', alist' = rename_sub used subst_free vs in
      (match alist' with
       | [] -> exists vs (aux alist f)
       | _ ->
         let f' = replace_formula_vars_rename ~used:used' alist' f in
         exists vs' (aux alist f'))
    | Ctx (cvars, f) -> ctx cvars (aux alist f)
    | Prop (p, tmlst) -> prop p (List.map (term_aux alist) tmlst)
  in
  aux alist t
;;

let rec copy_formula f =
  match f with
  | All (vs, body) ->
    let vs' = List.map (fun (n, ty) -> var Eigen n 0 ty) vs in
    let body' =
      copy_formula (replace_formula_vars (List.map2 (fun (n, _) tm -> n, tm) vs vs') body)
    in
    forall vs body'
  | Exists (vs, body) ->
    let vs' = List.map (fun (n, ty) -> var Eigen n 0 ty) vs in
    let body' =
      copy_formula (replace_formula_vars (List.map2 (fun (n, _) tm -> n, tm) vs vs') body)
    in
    exists vs body'
  | Ctx (vs, body) -> ctx vs (copy_formula body)
  | Imp (l, r) -> imp (copy_formula l) (copy_formula r)
  | And (l, r) -> f_and (copy_formula l) (copy_formula r)
  | Or (l, r) -> f_or (copy_formula l) (copy_formula r)
  | _ -> f
;;

let rec norm f =
  match f with
  | Top | Bottom | Atm _ | Prop _ -> f
  | Imp (l, r) -> Imp (norm l, norm r)
  | And (l, r) -> And (norm l, norm r)
  | Or (l, r) -> Or (norm l, norm r)
  | Ctx (gs, f') ->
    (match norm f' with
     | Ctx (gs', f'') -> ctx (gs @ gs') f''
     | f'' -> ctx gs f'')
  | All (vs, f') ->
    (match norm f' with
     | All (vs', f'') -> forall (vs @ vs') f''
     | f'' -> forall vs f'')
  | Exists (vs, f') ->
    (match norm f' with
     | Exists (vs', f'') -> exists (vs @ vs') f''
     | f'' -> exists vs f'')
;;

let rec eta_expand (f : formula) =
  match f with
  | Top | Bottom -> f
  | Atm (g, m, t, a) -> Atm (g, Term.eta_expand m, Term.eta_expand t, a)
  | Ctx (c, f') -> Ctx (c, eta_expand f')
  | All (t, f') -> All (t, eta_expand f')
  | Exists (t, f') -> Exists (t, eta_expand f')
  | Imp (f1, f2) -> Imp (eta_expand f1, eta_expand f2)
  | And (f1, f2) -> And (eta_expand f1, eta_expand f2)
  | Or (f1, f2) -> Or (eta_expand f1, eta_expand f2)
  | Prop (i, ts) -> Prop (i, List.map Term.eta_expand ts)
;;

let block_sim f ctx_var sub_rel b1 b2 =
  let rec aux = function
    | Top | Bottom | Prop _ -> true
    | Imp (l, r) | Or (l, r) | And (l, r) -> aux l && aux r
    | Atm (g, _, a, _) when g = Context.Var ctx_var ->
      Context.block_eq_sub sub_rel (Term.get_ty_head a) b1 b2
    (* Only supports contexts which only contain a context variable *)
    | Atm (g, _, _, _) when Context.get_ctx_var g = ctx_var -> false
    | Atm _ -> true
    | Ctx (cvars, f) -> List.exists (fun (cv, _) -> cv = ctx_var) cvars || aux f
    | All (_, f) | Exists (_, f) -> aux f
  in
  aux f
;;

let block_in_schema_sub f ctx_var sub_rel b c =
  let get_block_types (B (_, entries)) =
    List.map (fun (_, t) -> Term.get_ty_head t) entries
  in
  let context_types = List.flatten_map get_block_types c in
  List.exists
    (fun schema_block ->
      block_prefix_sub sub_rel context_types schema_block b
      && block_sim f ctx_var sub_rel b schema_block)
    c
;;

let schema_transports f ctx_var sub_rel c1 c2 =
  List.for_all (fun block -> block_in_schema_sub f ctx_var sub_rel block c2) c1
;;

(* Apply the given context variable substitution within the given formula. *)
let rec replace_ctx_vars ctxvar_subst f =
  match f with
  | Top | Bottom | Prop _ -> f
  | Imp (l, r) -> imp (replace_ctx_vars ctxvar_subst l) (replace_ctx_vars ctxvar_subst r)
  | And (l, r) ->
    f_and (replace_ctx_vars ctxvar_subst l) (replace_ctx_vars ctxvar_subst r)
  | Or (l, r) -> f_or (replace_ctx_vars ctxvar_subst l) (replace_ctx_vars ctxvar_subst r)
  | All (vs, f) -> forall vs (replace_ctx_vars ctxvar_subst f)
  | Exists (vs, f) -> exists vs (replace_ctx_vars ctxvar_subst f)
  | Ctx (bndrs, f') ->
    let subst' = List.remove_assocs (List.map fst bndrs) ctxvar_subst in
    let used = Context.get_used_ctxvars (List.map snd ctxvar_subst) in
    let bnd_subst =
      let used = ref used in
      List.map
        (fun (x, _) ->
          let fresh, used' = Context.fresh_wrt x !used in
          used := used';
          x, Context.Var fresh)
        bndrs
    in
    ctx
      (List.map2 (fun (_, s) (_, g) -> Context.get_ctx_var g, s) bndrs bnd_subst)
      (replace_ctx_vars (subst' @ bnd_subst) f')
  | Atm (g, m, a, ann) ->
    if Context.has_var g
    then (
      match List.assoc_opt (Context.get_ctx_var g) ctxvar_subst with
      | Some g' -> atm ~ann (Context.replace_ctx_vars [ Context.get_ctx_var g, g' ] g) m a
      | None -> f)
    else f
;;

let get_compatible_context_schemas schemas sub_rel f =
  let rec collect_bindings f =
    match norm f with
    | Ctx (cvars, f') -> cvars @ collect_bindings f'
    | All (_, f') -> collect_bindings f'
    | _ -> []
  in
  let get_compatible_schemas (ctx_var, schema_name) =
    let ctx_var_schema = List.assoc_opt schema_name schemas in
    match ctx_var_schema with
    | None -> []
    | Some ctx_var_schema ->
      schemas
      |> List.filter (fun (_, schema) ->
        schema_transports f ctx_var sub_rel schema ctx_var_schema)
      |> List.map fst
  in
  collect_bindings f |> List.map (fun x -> fst x, get_compatible_schemas x)
;;

let occurs_negatively (ctx_var : ctx_var) (f : formula) =
  let rec pos matcher f =
    match f with
    | Top -> true
    | Bottom | Prop _ | Atm _ -> false
    | Ctx (bndrs, f') ->
      (* If there is a quantifier that shadows [ctx_var] then we want to only check if the
         structural properties hold *)
      if List.map fst bndrs |> List.mem ~cmp:(fun _ x -> matcher x) ctx_var
      then pos (fun _ -> false) f'
      else pos matcher f'
    | All (_, f') | Exists (_, f') -> pos matcher f'
    | Imp (f1, f2) -> neg matcher f1 || pos matcher f2
    | And (f1, f2) -> pos matcher f1 && pos matcher f2
    | Or (f1, f2) -> pos matcher f1 || pos matcher f2
  and neg matcher f =
    match f with
    | Bottom -> true
    | Top | Prop _ -> false
    | Atm (g, _, _, _) ->
      if Context.has_var g
      then (
        let ctx_var' = Context.get_ctx_var g in
        if matcher ctx_var' then true else false)
      else false
    | Ctx (bndrs, f') ->
      (* If there is a quantifier that shadows [ctx_var] then we want to only check if the
         structural properties hold *)
      if List.map fst bndrs |> List.mem ~cmp:(fun _ x -> matcher x) ctx_var
      then neg (fun _ -> false) f'
      else neg matcher f'
    | All (_, f') | Exists (_, f') -> neg matcher f'
    | Imp (f1, f2) -> pos matcher f1 && neg matcher f2
    | And (f1, f2) -> neg matcher f1 || neg matcher f2
    | Or (f1, f2) -> neg matcher f1 && neg matcher f2
  in
  pos (fun x -> x = ctx_var) f
;;
