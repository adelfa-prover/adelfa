(*
 *
 * SEQUENT
 * Representation of a sequent/subgoal.
 * 
 *
 *)
open Extensions

type tag =
  | Explicit
  | Implicit

type hyp =
  { id : string
  ; tag : tag
  ; formula : Formula.formula
  }

type cvar_entry = Context.ctx_var * Term.id list ref * Context.ctx_typ

let cp_cvar_entry (id, restricted, blocks) =
  let names = !restricted in
  let cp = ref names in
  id, cp, blocks
;;

type sequent =
  { mutable vars : (Term.id * Term.term) list
  ; mutable ctxvars : cvar_entry list
  ; mutable hyps : hyp list
  ; mutable goal : Formula.formula
  ; mutable count : int
  ; mutable name : string
  ; mutable next_subgoal_id : int
  }

let cp_sequent sq =
  { sq with vars = sq.vars; ctxvars = List.map cp_cvar_entry sq.ctxvars }
;;

let assign_sequent sq1 sq2 =
  sq1.vars <- sq2.vars;
  sq1.ctxvars <- sq2.ctxvars;
  sq1.hyps <- sq2.hyps;
  sq1.goal <- sq2.goal;
  sq1.count <- sq2.count;
  sq1.name <- sq2.name;
  sq1.next_subgoal_id <- sq2.next_subgoal_id
;;

let add_var sequent (id, tm) =
  if not (List.mem_assoc id sequent.vars)
  then sequent.vars <- (id, tm) :: sequent.vars
  else
    sequent.vars
      <- List.map (fun (name, t) -> if id = name then name, tm else name, t) sequent.vars
;;

let remove_var sequent id =
  sequent.vars <- List.remove_all (fun (n, _) -> id = n) sequent.vars
;;

let add_if_new_var sequent (id, tm) =
  if not (List.mem_assoc id sequent.vars) then add_var sequent (id, tm)
;;

(* add_var sequent (id,tm) *)

let get_nominals sequent =
  List.filter (fun (_, t) -> Term.is_var Term.Nominal t) sequent.vars
;;

(** Generates a new eigenvariable in relation to [sequent]
    @param sequent the sequent to generate an eigenvariable for *)
let get_eigen sequent = List.filter (fun (_, t) -> Term.is_var Term.Eigen t) sequent.vars

let add_ctxvar sequent c ?rstrct:(r = []) t =
  sequent.ctxvars <- (c, ref r, t) :: sequent.ctxvars
;;

let remove_ctxvar sequent v =
  sequent.ctxvars
    <- List.filter (fun (c, _, _) -> not (Context.ctx_var_eq v c)) sequent.ctxvars
;;

let get_ctxvar_restricted (_, rstrct, _) = !rstrct
let get_assoc_ctxvar_restricted (id, rstrct, _) = id, !rstrct
let get_assoc_ctxvars_restricted entries = List.map get_assoc_ctxvar_restricted entries

let replace_assoc_ctxvars_restricted alist entries =
  let alist = List.map (fun (v, t) -> v, Term.term_to_name t) alist in
  let rec aux entry =
    match entry with
    | [] -> []
    | x :: xs ->
      (match List.assoc_opt x alist with
       | None -> x :: aux xs
       | Some x' -> x' :: aux xs)
  in
  List.map (fun (v, vars) -> v, aux vars) entries
;;

let get_ctxvar_id (id, _, _) = id
let get_ctxvar_ty (_, _, ctxty) = ctxty

(* This function will update the given context variable context entry 
   to add ns to the collection of restricted names. Returns the
   updated context variable entry. *)
let restrict_in ((_, rstrct, _) as cvar) ns =
  rstrct := ns @ !rstrct;
  cvar
;;

let ctxvar_mem cvars n = List.exists (fun (var, _, _) -> Context.ctx_var_eq n var) cvars

(* Raises Not_found if context variable does not appear. *)
let ctxvar_lookup cvars n = List.find (fun (var, _, _) -> Context.ctx_var_eq n var) cvars
let get_cvar_tys cvars = List.map (fun (x, _, z) -> x, z) cvars

(* apply susbtitution to eigenvariables in sequent.
   Does not modify Psi (eigenvariable context) to reflect the substitution;
   assumes this is handled by the caller. *)
let replace_seq_vars subst sequent =
  sequent.vars <- sequent.vars;
  sequent.ctxvars
    <- List.map
         (fun (v, rstrct, ctxty) -> v, rstrct, Context.replace_ctx_typ_vars subst ctxty)
         sequent.ctxvars;
  sequent.hyps
    <- List.map
         (fun h ->
           { id = h.id
           ; tag = h.tag
           ; formula = Formula.replace_formula_vars subst h.formula
           })
         sequent.hyps;
  sequent.goal <- Formula.replace_formula_vars subst sequent.goal;
  sequent.count <- sequent.count;
  sequent.name <- sequent.name;
  sequent.next_subgoal_id <- sequent.next_subgoal_id
;;

let remove_trailing_numbers s =
  let rec scan i =
    if i < 0
    then 0
    else (
      match s.[i] with
      | '0' .. '9' -> scan (i - 1)
      | _ -> i + 1)
  in
  let len = scan (String.length s - 1) in
  String.sub s 0 len
;;

let fresh_name name used =
  let basename = remove_trailing_numbers name in
  let rec aux i =
    let name = basename ^ string_of_int i in
    if List.mem name used then aux (i + 1) else name
  in
  (* Try to avoid any renaming *)
  if List.mem name used then aux 1 else name
;;

let fresh_hyp_name sequent base =
  if base = ""
  then (
    sequent.count <- sequent.count + 1;
    "H" ^ string_of_int sequent.count)
  else fresh_name base (List.map (fun h -> h.id) sequent.hyps)
;;

let make_hyp sequent ?(name = "") ?(tag = Explicit) form =
  let name = fresh_hyp_name sequent name in
  { id = name; formula = form; tag }
;;

let add_hyp sequent ?(name = "") form =
  sequent.hyps <- List.append sequent.hyps [ make_hyp sequent ~name form ]
;;

let get_hyp sequent name = List.find (fun h -> h.id = name) sequent.hyps

let remove_hyp sequent name =
  sequent.hyps <- List.remove_all (fun h -> h.id = name) sequent.hyps
;;

let replace_hyp sequent name f =
  let rec aux hyplist =
    match hyplist with
    | [] -> []
    | hyp :: rest when hyp.id = name -> { hyp with formula = f } :: rest
    | hyp :: rest -> hyp :: aux rest
  in
  sequent.hyps <- aux sequent.hyps
;;

(* If the given formula is atomic then normalizes the form to be a *)
(* typing judgment for an atomic term/type.*)
let norm_atom sequent formula =
  let rec aux formula =
    match formula with
    | Formula.Atm (g, m, a, ann) ->
      (match Term.observe (Term.hnorm a) with
       | Term.Pi ((v, typ) :: bndrs, body) ->
         (* for each binder introduce new name n, raise relevant eigenvariables over n,
             then move into context and apply term component to this n. *)
         let used = get_nominals sequent in
         let name, _ = Term.fresh_wrt ~ts:2 Nominal "n" v.Term.ty used in
         let _ = add_var sequent (Term.term_to_pair name) in
         if Context.has_var g
         then (
           let _ =
             restrict_in
               (ctxvar_lookup sequent.ctxvars (Context.get_ctx_var g))
               [ Term.get_id name ]
           in
           ());
         let g' = Context.Ctx (g, (Term.term_to_var name, typ)) in
         let m' = Term.app m [ Term.eta_expand name ] in
         let a' =
           Term.replace_term_vars
             [ v.Term.name, Term.eta_expand name ]
             (Term.pi bndrs body)
         in
         aux (Formula.atm ~ann g' m' a')
       | _ -> formula)
    | _ -> formula
  in
  aux formula
;;

(* Introduce new eigenvariables for quantifiers at the top-level. *)
let exists_left sequent formula =
  let rec aux formula =
    match formula with
    | Formula.Exists (vs, f) ->
      let support =
        List.map snd (List.filter (fun (_, t) -> Term.is_var Term.Nominal t) sequent.vars)
      in
      let used =
        ref (List.filter (fun (_, t) -> Term.is_var Term.Eigen t) sequent.vars)
      in
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
      aux
        (Formula.replace_formula_vars
           (List.map2 (fun (n, _) (_, t) -> n, Term.app t support) vs new_vars)
           f)
    | _ -> formula
  in
  aux formula
;;

(* Normalization for formulas appearing on the left(assumptions). *)
(* Currently normal form of assumptions introduces eigenvariables for *)
(* existentials at the top level and reduces atomic formulas to typing *)
(* judgments over atomic terms/types. *)
let norm sequent formula =
  let rec aux formula =
    match formula with
    | Formula.Exists _ -> aux (exists_left sequent formula)
    | Formula.Atm _ -> norm_atom sequent formula
    | _ -> formula
  in
  aux formula
;;

let normalize_formula sequent id formula =
  let f = norm sequent formula in
  replace_hyp sequent id f
;;

let normalize_hyps sequent =
  let hyp_ids = List.map (fun h -> h.id) sequent.hyps in
  let update id =
    let new_form = norm sequent (get_hyp sequent id).formula in
    replace_hyp sequent id new_form
  in
  List.iter update hyp_ids
;;

let make_sequent_from_goal ?(name = "") ~form:goal () =
  { vars = List.map Term.term_to_pair (Formula.formula_support [] goal)
  ; ctxvars = []
  ; hyps = []
  ; goal
  ; count = 0
  ; name
  ; next_subgoal_id = 1
  }
;;
