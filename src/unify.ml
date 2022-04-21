(* UNIFY
 * Pattern unification of terms.
 *)

(** Higher Order Pattern Unification *)

(* Note that even though we only currently use unification in one 
 * context, case analysis, I leave the modulized structure of 
 * unification from Abella in case we wish to implement other 
 * instances in future. *)

open Term
open Extensions
              
(* generate ids for n binders *)
let gen_binder_ids n =
  List.map (fun i -> ("z"^(string_of_int i))) (List.range 1 n)

type unify_failure =
  | OccursCheck
  | ConstClash of (term * term)
  | Generic
  | FailTrail of int * unify_failure

let rec explain_failure = function
  | OccursCheck -> "Unification failure (occurs-check)"
  | ConstClash (t1, t2) ->
      Printf.sprintf "Unification failure (constant clash between %s and %s)"
        (Print.string_of_term t1) (Print.string_of_term t2)
  | Generic -> "Unification failure"
  | FailTrail (n, fl) ->
      Printf.sprintf "While matching argument #%d:\n%s" n (explain_failure fl)

exception UnifyFailure of unify_failure

let fail f = raise (UnifyFailure f)

type unify_error =
  | NotLLambda

let explain_error = function
  | NotLLambda -> "Unification incompleteness (non-pattern unification problem)"

exception UnifyError of unify_error

(* An explicit handler is specified for how to deal with
   non-llambda conflict pairs *)
module type Param =
sig
  val instantiatable : tag
  val constant_like  : tag
  val handler : term -> term -> unit
end

module Make (P:Param) =
struct

open P

let local_used = ref []

let named_fresh name ts ty =
  let (v, new_used) = fresh_wrt ~ts instantiatable name ty !local_used in
    local_used := new_used ;
    v
    (* Term.eta_expand v *)

  
(* Note: we do not allow nominals in substitution terms. 
 * They are only able to appear through explicit dependencies. *)
let constant tag =
  tag = Constant || tag = constant_like || tag = Nominal 
let variable tag =
  tag = instantiatable

(* Return the number of abstractions need to make a term closed *)
let closing_depth t =
  let rec aux t =
    match observe (hnorm t) with
      | Var _ -> 0
      | DB i -> i
      | Lam(idtys, t) -> max (aux t - List.length idtys) 0
      | App(h, ts) -> List.max (List.map aux (h :: ts))
      | _ -> assert false
  in
    aux t

(* Transforming a term to represent substitutions under abstractions *)
let lift t n =
  match observe t with
    | Var _ -> t
    | DB i -> db (i+n)
    | _ -> susp t 0 n []

(* Transforming a list of arguments to represent eta fluffing *)
let rec lift_args l n =
  match l,n with
    | [],0 -> []
    | [],n -> (db n)::lift_args [] (n-1)
    | (a::rargs),n -> (lift a n)::lift_args rargs n

(* Check wether a Var appears in a list of terms *)
let rec unique_var v = function
  | [] -> true
  | t::rargs  ->
      begin match observe t with
        | Var v' when v=v' -> false
        | _ -> unique_var v rargs
      end

(* Check if a bound variable appears in a list of term *)
let rec unique_bv n l = match l with
  | [] -> true
  | t::rargs ->
      begin match observe t with
        | DB j when n = j -> false
        | _ -> unique_bv n rargs
      end
        
(** [check_flex_args l fts] checks that a list of terms meets the LLambda
  * requirements for the arguments of a flex term whose timestamp is [fts]. *)
(* Added: will check if the eta-normal form of the list meets Llambda requirements *)
let check_flex_args l fts =
  let rec aux = function
    | [] -> (true, [])
    | t::ts ->
        match (observe t) with
          | Var v when constant v.tag && v.ts>fts && unique_var v ts ->
              let (res, l') = aux ts in (res, Var v :: l')
          | DB i when unique_bv i ts ->
            let (res, l') = aux ts in (res, DB i :: l')
          | _ ->
            (false, l)
  in
    aux (List.map eta_normalize l)

(** [ensure_flex_args l fts] ensures that a list of terms meets the LLambda
  * requirements for the arguments of a flex term whose timestamp is [fts].
  * @raise NotLLambda if the list doesn't satisfy the requirements. *)
let ensure_flex_args l fts =
  let (res,_) = check_flex_args l fts in
  if not res then
    raise (UnifyError NotLLambda)

(** [bvindex bv l n] return a nonzero index iff the db index [bv]
  * appears in [l]; the index is the position from the right, representing
  * the DeBruijn index of the abstraction capturing the argument.
  * Arguments in the list are expected to be head-normalized. *)
let rec bvindex i l n = match l with
  | [] -> 0
  | t::q ->
     begin match observe (eta_normalize t) with
       | DB j when i=j -> n
       | _ -> bvindex i q (n-1)
     end

(** [cindex c l n] return a nonzero index iff the constant [c]
  * appears in [l]; the index is the position from the right, representing
  * the DeBruijn index of the abstraction capturing the argument.
  * Arguments in the list are expected to be head-normalized. *)
let rec cindex c l n = match l with
  | [] -> 0
  | t::q ->
      begin match observe (eta_normalize t) with
        | Var c' when c = c' -> n
        | _ -> cindex c q (n-1)
      end

(** Given a flexible term [v1 a11 ... a1n] and another term of the form
  * [... (v2 a21 ... a2m) ...] where [v1] and [v2] are distinct variables,
  * [ts1] and [ts2] being the timestamps associated with [v1] and [v2],
  * and [lev] being the number of abstractions under which [v2] appears
  * embedded in the second term,
  * [raise_and_invert ts1 ts2 [a11 .. a1n] [a21 .. a2m] lev]
  * return a triple consisting of:
  *
  * {ul
  * {li a truth value indicating whether a pruning or raising
  * substitution is needed for [v2],}
  * {li a list of terms [b1 ... bk] such that the term
  * [Lam ... Lam (... (v2' b1 ... bk) ...]
  * represents a unifying substitution for [v1] -- these terms
  * consist of constants from [a11 ... a1n] over which [v2] is
  * possibly raised and inversions of a pruned [a21 ... a2m], and}
  * {li the arguments [c1 ... ck] of a possible "raising" and pruning
  * substitution for [v2] matching the arguments [b1 ... bk] for
  * [v2'] in the second component.}}
  *
  * The composition of the arguments lists can be understood
  * qualitatively as follows:
  *
  * If [ts1 < ts2] then {ul{li the initial part of
  * [b1 ... bk] is the indices of constants from [a11 ... a1n] that do
  * not appear in [a21 ... a2m] and that have a timestamp less than or
  * equal to [ts2] (this corresponds to raising [v2]) and} {li the rest of
  * [b1 ... bk] are the indices (relative to the list a11 ... a1n) of
  * the constants in [a21 ... a2m] that appear in [a11 ... a1n] (these are
  * the arguments that must not be pruned).}} Correspondingly, the first
  * part of the list [c1 ... ck] are the constants from [a11 ... a1n] over
  * which [v2] is "raised" and the second part are the indices relative
  * to [a21 ... a2m] of the constants that are not pruned.
  *
  * If [ts1 >= ts2]
  * then each of [b1 ... bk] is either {ul{li a constant in [a21 ... a2m] that
  * does not appear in [a11 ... a1n] and which has a timestamp less than
  * [ts1] (this corresponds to first raising [v1] and then reducing the
  * substitution generated for [v1])} {li or it is the index, relative to
  * [a11 ... a1n], of the terms in [a21 ... a2m] that are in
  * [a11 ... a1n].}}
  * The list [c1 ... ck] in this case are simply the indices
  * relative to [a21 ... a2m] of the terms in [a21 ... a2m] that are
  * preserved (i.e. not pruned) in [b1 ... bk].
  *
  * This definition assumes that the [aij] are in
  * head-normal form and that [a1] satisfies the LLambda
  * requirements. If [a2] does not satisfy these requirements, an
  * exception will be raised. *)
let raise_and_invert ts1 ts2 a1 a2 lev =
  let l1 = List.length a1 in

  (* [raise_var args n] generates the collection of
   * constants in [args] that have a time stamp less than [ts2],
   * assuming [n] is the index for the abstraction corresponding
   * to the first term in [args]. In other words, constants which cannot
   * appear in [v2]'s body. This
   * serves to raise [v2] in the case where [ts1 < ts2]. The boolean
   * component of the returned triple tells if there is
   * any raising to be done. The terms in [args] are assumed to be
   * constants or de Bruijn indices, as head normalized
   * arguments satisfying the LLambda restriction. *)
  let rec raise_var l n = match l with
    | [] -> false,[],[]
    | t::tl ->
        begin match observe t with
          | DB _ -> raise_var tl (n-1)
          | Var c when constant c.tag ->
              let raised,inds,consts = raise_var tl (n-1) in
                if c.ts<=ts2
                then (true,(db (n+lev))::inds,t::consts)
                else (raised,inds,consts)
          | _ -> assert false
        end
  in

  (*  [prune args n] "prunes" those items in [args] that are not
      bound by an embedded abstraction and that do not appear in
      [a1]. At the same time inverts the items that are not pruned
      and that are not bound by an embedded abstraction; [n] is assumed to be
      the length of [args] here and hence yields the index of the
      leftmost argument position. This pruning computation is
      relevant to the case when [ts1 < ts2]. The terms in [args]
      are assumed to be constants or de Bruijn indices. *)
  let rec prune l n = match l,n with
    | [],0 -> false,[],[]
    | t::q,n ->
        begin match observe t with
          | DB i ->
              let pruned,inds1,inds2 = prune q (n-1) in
                if i > lev then
                  let j = bvindex (i-lev) a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (db (j+lev))::inds1,
                       (db n)::inds2)
                else
                  (pruned,t::inds1,(db n)::inds2)
          | Var v when constant v.tag ->
              let (pruned,inds1,inds2) = prune q (n-1) in
              let j = cindex v a1 l1 in
                if j = 0 then
                  (true,inds1,inds2)
                else
                  (pruned,
                   (db (j+lev))::inds1,
                   (db n)::inds2)
          | _ -> assert false
        end
    | _ -> assert false
  in

  (*  Relevant to the case when [ts1 > ts2]. In this case,
      [prune_and_raise args n] prunes those constants and de
      Bruijn indices not bound by an embedded abstraction that do
      not appear in [a1] and, in the case of constants, that do not
      have a timestamp less than [ts1]. Constants that do have a timestamp
      greater than or equal to [ts1] are preserved via a raising of
      [v1]. As in prune, [n] is assumed to be the length of the list
      args. The terms in [args] are assumed to be constants or de
      Bruijn indices. *)
  let rec prune_and_raise l n = match l,n with
    | [],0 -> false,[],[]
    | a::q,n ->
        begin match observe a with
          | DB i ->
              let (pruned,inds1,inds2) = prune_and_raise q (n-1) in
                if i > lev then
                  let j = bvindex (i-lev) a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (db (j+lev))::inds1,
                       (db n)::inds2)
                else (pruned,a::inds1,(db n)::inds2)
          | Var v when constant v.tag ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
                if v.ts <= ts1 then
                  (pruned,a::inds1,(db n)::inds2)
                else
                  let i = cindex v a1 l1 in
                    if i=0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (db (i+lev))::inds1,
                       (db n)::inds2)
          | _ -> assert false
        end
    | _ -> assert false
  in

    if ts1<ts2 then
      let raised,args11,args12 = raise_var a1 l1 in
      let pruned,args21,args22 = prune a2 (List.length a2) in
        (raised||pruned,args11@args21,args12@args22)
    else
      prune_and_raise a2 (List.length a2)

(* Generating the arguments of a pruning substitution for the case
 * when trying to unify two flexible terms of the form (v t1 ... tn)
 * and lam ... lam (v s1 ... sm) where there are j abstractions at the
 * head of the second term. The first two arguments to prune_same_var
 * are the two lists of arguments, the third argument is j (i.e. the
 * number of abstractions at the head) and the last argument is n+j. It
 * is assumed that type consistency has been checked beforehand,
 * i.e. n+j is indeed equal to m and also that the two argument lists
 * are known to be of the form required for LLambda unification. The
 * computation essentially does the eta fluffing of the first term on
 * the fly (i.e. each ti has to be lifted over j abstractions and and
 * j new arguments bound by these abstractions are added to the first
 * term). *)
let rec prune_same_var l1 l2 j bl = match l1,l2 with
  | [],[] -> []
  | [],t::q ->
      begin match observe t with
        | DB i when i=j ->
            (db bl)::(prune_same_var [] q (j-1) (bl-1))
        | _ -> prune_same_var [] q (j-1) (bl-1)
      end
  | t1::a1,t2::a2 ->
      begin match observe t1,observe t2 with
        | Var v1,Var v2
          when v1 = v2 && constant v1.tag ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | DB i1,DB i2     when i1+j = i2 ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | _ -> prune_same_var a1 a2 j (bl-1)
      end
  | _ -> assert false

(* Given a variable [v1] which has access to the terms [a11 ... a1n] via
 * de Bruijn indices,
 *   [make_non_llambda_subst v1 a1 t2]
 * returns a substitution for [v1] which unifies it with [t2]. Here it is
 * assumed that [a1] satisfies the LLambda restriction, but [t2] might not. If
 * a substitution cannot be found due to non-LLambda issues, an error exception
 * is thrown. *)
let make_non_llambda_subst v1 a1 t2 =
  let a1 = List.map hnorm a1 in
  let n = List.length a1 in
  let rec aux lev t =
    match observe (hnorm t) with
      | Var v when variable v.tag && v <> v1 && v.ts <= v1.ts ->
          t
      | Var v when constant v.tag && v1.ts < v.ts ->
          let i = cindex v a1 n in
            if i = 0 then
              raise (UnifyError NotLLambda)
            else
              db (i+lev)
      | DB i ->
          if i <= lev then t else
            let j = bvindex (i-lev) a1 n in
              if j = 0 then
                raise (UnifyError NotLLambda)
              else
                db (j+lev)
      | App(h2,a2) ->
          app (aux lev h2) (List.map (aux lev) a2)
      | Lam(idtys2,b2) ->
          lambda idtys2 (aux (lev + List.length idtys2) b2)
      | _ -> raise (UnifyError NotLLambda)
  in
    aux 0 t2

(* Here we assume v1 is a variable we want to bind to t2. We must check that
 * there is no-cyclic substitution and that nothing with a timestamp higher
 * than t1 is allowed. A more general check is possible here, but this
 * should suffice. *)
let rigid_path_check v1 t2 =
  let rec aux n t =
    match observe (hnorm t) with
      | Var v -> (v1 <> v) && (v.ts <= v1.ts)
      | DB i -> i <= n
      | Lam(idtys, t) -> aux (n + List.length idtys) t
      | App(h, ts) -> List.for_all (aux n) (h::ts)
      | _ -> assert false
  in
    aux 0 t2

(* Assuming t2 is a variable which we want to bind to t1, we try here to
 * instead bind some pruned version of t1 to t2. Doing this allows us to
 * avoid generating a new name.
 *
 * Example: Instead of binding X^0 to Y^0 c^1, we bind Y^0 to z\ X^0
 *)
let reverse_bind (tyctx:(Term.id*Type.ty) list) t1 t2 =
  match observe t1, observe t2 with
    | App(h, ts), Var v2 ->
        let pruneable t =
          begin match observe (hnorm t) with
            | Var c when constant c.tag && v2.ts < c.ts -> true
            | DB _ -> true
            | _ -> false
          end
        in
          begin match observe h with
            | Var v1 when variable v1.tag && v2.ts <= v1.ts &&
                List.for_all pruneable ts ->
                  let ids = gen_binder_ids (List.length ts) in
                  let tys = List.map (tc tyctx) ts in
                  (bind h (lambda (List.combine ids tys) t2); true)
            | _ -> false
          end
    | Var v1, Var v2 when variable v1.tag && v1.ts > v2.ts ->
        bind t1 t2 ;
        true
    | _ -> false

(** [makesubst tyctx h1 t2 a1 n] unifies [App (h1,a1) = t2].
    * Given a term of the form [App (h1,a1)] where [h1] is a variable and
    * another term [t2], generate an LLambda substitution for [h1] if this is
    * possible, making whatever pruning and raising substitution that are
    * necessary to variables appearing within [t2].
    *
    * [t2] is assumed to be in head normal form, [h1] and [a1] are assumed to be
    * dereferenced, and [n] is supposed to be the length of [a1].
    *
    * Exceptions can be
    * raised from this code if a non LLambda situation is discovered or
    * there is failure in unification or a type mismatch (possible if an
    * a priori type checking has not been done) is encountered.
    *
    * The unification computation is split into two parts, one that
    * examines the top level structure of [t2] and the other that descends
    * into its nested subparts. This organization is useful primarily
    * because [h1], the variable head of the first term can appear at the
    * toplevel in t2 without sacrificing unifiability but not in a nested
    * part. *)
let makesubst tyctx h1 t2 a1 n =
  (* Check that h1 is a variable, get its timestamp *)
  let hv1 = match observe h1 with
    | Var v -> assert (variable v.tag) ; v
    | _ -> assert false
  in
  let ts1 = hv1.ts in
  let a1 = List.map hnorm a1 in

  (*  Generating a substitution term and performing raising and
      pruning substitutions corresponding to a non top-level
      (sub)term. In this case the variable being bound cannot appear
      embedded inside the term. This code assumes that its term
      * argument is head normalized. Exceptions can be
      raised if unification fails or if LLambda conditions are found
      to be violated. *)
  let rec nested_subst tyctx c lev =
    match observe c with
      | Var v when constant v.tag ->
          (* Can [h1] depend on [c] ?
           * If so, the substitution is [c] itself.
           * If not, [c] must belong to the argument list. *)
          if v.ts <= ts1 then c else
            let j = cindex v a1 n in
              if j = 0 then fail Generic ;
              db (j+lev)
      | DB i ->
          if i<=lev then c else
            let j = bvindex (i-lev) a1 n in
              if j = 0 then fail Generic ;
              db (j+lev)
      | Var v when variable v.tag ->
          if eq c h1 then fail OccursCheck ;
          let (changed,a1',a2') = raise_and_invert ts1 v.ts a1 [] lev in
            if changed || ts1 < v.ts then
              let ty = Type.tyarrow (List.map (tc tyctx) a2') (tc tyctx c) in
              let h' = named_fresh hv1.name (min ts1 v.ts) ty in
                bind c (app h' a2') ;
                app h' a1'
            else
              app c a1'
      | Lam (idtys,t) ->
        lambda idtys
          (nested_subst (List.rev_append idtys tyctx) t (lev + List.length idtys))
            
      | App (h2,a2) ->
          begin match observe h2 with
            | Var hv2 when constant hv2.tag ->
                let h2' = nested_subst tyctx h2 lev in
                let a2' =
                  List.map (fun x -> nested_subst tyctx (hnorm x) lev) a2
                in
                  app h2' a2'
            | DB _ ->
                let h2' = nested_subst tyctx h2 lev in
                let a2' =
                  List.map (fun x -> nested_subst tyctx (hnorm x) lev) a2
                in
                  app h2' a2'
            | Var hv2 when variable hv2.tag ->
                if eq h2 h1 then raise (UnifyError NotLLambda) ;
                let (res, a2) = check_flex_args a2 hv2.ts in
                  if res then
                    let changed,a1',a2' =
                      raise_and_invert ts1 hv2.ts a1 a2 lev
                    in
                      if changed then
                        let a2ids = gen_binder_ids (List.length a2) in
                        let a2binds = List.map (tc tyctx) a2 in
                        let a2ctx = List.combine a2ids a2binds in
                        let a2'tys =
                          List.map (tc (List.rev_append a2ctx tyctx))
                                   a2' in
                        let Type.Ty(h2tys, bty) = tc tyctx h2 in
                        let ty = Type.Ty(a2'tys @ List.drop (List.length a2
                                                       ) h2tys, bty)
                        in
                        let h' = named_fresh  hv1.name (min ts1 hv2.ts)
                                             ty
                        in
                        bind h2 (lambda a2ctx (app h' a2')) ;
                        app h' a1'
                      else 
                        if ts1<hv2.ts then
                          let ty = tc tyctx h2 in
                          let h' = named_fresh  hv1.name ts1 ty in
                            bind h2 h' ;
                            app h' a1'
                        else
                          app h2 a1'
                  else
                    make_non_llambda_subst hv1 a1 c
            | Var _ -> failwith "logic variable on the left (1)"
            | _ -> assert false
          end
      | Var _ -> failwith "logic variable on the left (2)"
      | _ -> assert false
  in

  (*  Processing toplevel structure in generating a substitution.
      First descend under abstractions. Then if the term is a
      variable, generate the simple substitution. Alternatively, if
      it is an application with the variable being bound as its head,
      then generate the pruning substitution. In all other cases,
      pass the task on to nested_subst. An optimization is possible
      in the case that the term being examined has no outer
      abstractions (i.e. lev = 0) and its head is a variable with a
      time stamp greater than that of the variable being bound. In
      this case it may be better to invoke raise_and_invert
      directly with the order of the "terms" reversed.

      The incoming term is assumed to be head normalized.*)
  let rec toplevel_subst tyctx t2 lev =
    match observe t2 with
      | Lam (idtys,t2) ->
          lambda idtys
            (toplevel_subst (List.rev_append idtys tyctx) t2 (lev + List.length idtys))
      | Var v2 when variable v2.tag ->
          if h1=t2 then
            if n=0 && lev=0 then h1 else assert false (* fail TypesMismatch *)
          else begin
            if ts1 < v2.ts then
              Term.bind t2 (named_fresh v2.name ts1 v2.ty) ;
            t2
          end
      | App (h2,a2) ->
          begin match observe h2 with
            | Var hv2 when eq h1 h2 ->
                (* [h1] being instantiatable, no need to check it for [h2] *)
                let (res, a2) = check_flex_args a2 hv2.ts in
                  if res then
                    let bindlen = n+lev in
                      if bindlen = List.length a2 then
                        let args = prune_same_var a1 a2 lev bindlen in
                        let a2ids = gen_binder_ids bindlen in
                        let a2binds = List.map (tc tyctx) a2 in
                        let a2ctx = List.combine a2ids a2binds in
                        let args_ty =
                          List.map (tc (List.rev_append a2ctx tyctx)) args
                        in
                        let Type.Ty(h1tys, bty) = tc tyctx h1 in
                        let ty = Type.Ty(args_ty @ List.drop bindlen h1tys,
                                    bty) in
                        let h1' = named_fresh hv1.name ts1 ty in
                        app h1' args
                      else
                        assert false (* fail TypesMismatch *)
                  else
                    make_non_llambda_subst hv1 a1 t2
            | App _ | Lam _
            | Var _ | DB _ ->
                nested_subst tyctx t2 lev
            | Susp _ | Ptr _ | Type | Pi _ -> assert false
          end
      | Ptr _ -> assert false
      | _ ->
          nested_subst tyctx t2 lev
  in
  let a1ids = gen_binder_ids (List.length a1) in
  let a1tys = List.map (tc tyctx) a1 in
    (ensure_flex_args a1 ts1 ;
    lambda (List.combine a1ids a1tys) (toplevel_subst tyctx t2 0))

(** Unifying the arguments of two rigid terms with the same head, these
  * arguments being given as lists. Exceptions are raised if
  * unification fails or if there are unequal numbers of arguments; the
  * latter will not arise if type checking has been done. *)
let rec unify_list (tyctx:tyctx) l1 l2 =
  try
    List.iter2 (fun a1 a2 -> unify tyctx (hnorm a1) (hnorm a2)) l1 l2
  with
    | Invalid_argument _ -> assert false (* fail TypesMismatch *)

(* Unify [cst=t2], assuming [cst] is a constant.
 * Fail if [t2] is a variable or an application.
 * If it is a lambda, binders need to be equalized and so this becomes
 * an application-term unification problem. *)
and unify_const_term tyctx cst t2 =
  let v1 = term_to_var cst in
  match observe t2 with
    | Var v2 when constant v2.tag ->
      if v1 = v2
      then
        ()
      else
        fail (ConstClash (cst,t2))
    | Lam (idtys,t2) ->
        let a1 = lift_args [] (List.length idtys) in
          unify (List.rev_append idtys tyctx) (app cst a1) t2
    | Var v when not (variable v.tag || constant v.tag) ->
        failwith "logic variable on the left (3)"
    | _ -> fail (ConstClash (cst,t2))

(* Unify [App h1 a1 = t2].
 * [t1] should be the term decomposed as [App h1 a1].
 * [t2] should be dereferenced and head-normalized, not a var or lambda *)
and unify_app_term tyctx h1 a1 t1 t2 =
  match observe h1,observe t2 with
    | Var hv1, _ when variable hv1.tag ->
        let n = List.length a1 in
          bind h1 (makesubst tyctx h1 t2 a1 n)
    | Var v1, App (h2,a2) when constant v1.tag ->
        begin match observe h2 with
          | Var v2 when constant v2.tag ->
              if eq h1 h2 then
                unify_list tyctx a1 a2
              else
                fail (ConstClash (h1,h2))
          | DB _ ->
              fail (ConstClash (h1,h2))
          | Var hv2 when variable hv2.tag ->
              let m = List.length a2 in
                bind h2 (makesubst tyctx h2 t1 a2 m)
          | Var v when not (variable v.tag || constant v.tag) ->
              failwith "logic variable on the left (5)"
          | _ -> assert false
        end
    | DB n1, App (h2,a2) ->
        begin match observe h2 with
          | DB n2 when n1 == n2 ->
              unify_list tyctx a1 a2
          | Var v when variable v.tag ->
              let m = List.length a2 in
                bind h2 (makesubst tyctx h2 t1 a2 m)
          | Var v when constant v.tag -> fail (ConstClash (h1,h2))
          | Var v when not (variable v.tag || constant v.tag) ->
              failwith "logic variable on the left (5)"
          | _ -> assert false
        end
    | Lam _, _ | _, Lam _
    | Ptr _, _ | _, Ptr _
    | Susp _, _ | _, Susp _ -> assert false
    | Var v, _ when not (variable v.tag || constant v.tag) ->
        failwith "logic variable on the left (6)"
    | _ -> fail (ConstClash (h1,t2))

(* Unify [v1 = t2].
 * [t1] should be the term decomposed as [Var v1]. *)
and unify_var_term tyctx v1 t1 t2 =
  if reverse_bind tyctx t2 t1 then
    ()
  else if rigid_path_check v1 t2 then
    bind t1 t2
  else
    bind t1 (makesubst tyctx t1 t2 [] 0)

(* Unify [Lam(tys1,t1) = t2]. *)
and unify_lam_term tyctx tys1 t1 t2 =
  let n = List.length tys1 in
  unify
    (List.rev_append tys1 tyctx)
    t1
    (hnorm (app (lift t2 n) (lift_args [] n)))

(* Unify two type expressions t1 and t2. *)      
and unify_type_term tyctx tm1 tm2 =
  match observe tm1, observe tm2 with
  | Pi([],t1),Pi([],t2) -> unify_type_term tyctx t1 t2
  | Pi(((v1,ty1)::lftys1), t1),Pi(((_,ty2)::_),_) ->
    (unify_type_term tyctx ty1 ty2;
     unify_type_term
       ((v1.name, v1.ty)::tyctx)
       (pi lftys1 t1)
       (hnorm (app tm2 [(var_to_term v1)])))
  | App(h1,args1), App(h2,args2) when Term.eq h1 h2 ->
      (* Since types must be fully applied and the
         constant at the heads are the same, the two
         argument lists will be the same length. *)
    List.iter2 (unify tyctx) args1 args2
  | Var v1, Var v2 when v1 = v2 -> ()
  | Var _, Var _ -> fail (ConstClash(tm1, tm2))
  | App(h1,_), App(h2,_) ->
     fail (ConstClash (h1, h2))
  | _ ->
    (* Types are incompatible. *)
    fail Generic
    
(** The main unification procedure.
  * Either succeeds and realizes the unification substitutions as side effects
  * or raises an exception to indicate nonunifiability or to signal
  * a case outside of the LLambda subset. When an exception is raised,
  * it is necessary to catch this and at least undo bindings for
  * variables made in the attempt to unify. This has not been included
  * in the code at present.
  *
  * This procedure assumes that the two terms it gets are in
  * head normal form and that there are no iterated
  * lambdas or applications at the top level. Any necessary adjustment
  * of binders through the eta rule is done on the fly. *)
and unify (tyctx:tyctx) t1 t2 =
  (* print_endline ("Unifying:\n  "^(Print.string_of_term_literal t1)^"\nand\n  "^(Print.string_of_term_literal t2)); *)
  try match observe t1,observe t2 with
    (* New cases for unifying types. Since types must be 
       fully applied if both terms are not pi expressions
       them should fail. *)
    | Pi(_,_), Pi(_,_) -> unify_type_term tyctx t1 t2
    | Pi(_,_), _
    | _, Pi(_,_) -> fail Generic
    | Var v1, Var v2 when v1 = v2 -> ()
    | Var v1,_ when variable v1.tag -> unify_var_term tyctx v1 t1 t2
    | _,Var v2 when variable v2.tag -> unify_var_term tyctx v2 t2 t1
    | Lam(idtys1,t1),_    -> unify_lam_term tyctx idtys1 t1 t2
    | _,Lam(idtys2,t2)    -> unify_lam_term tyctx idtys2 t2 t1

    (* Check for a special case of asymmetric unification outside of LLambda *)
    | App(h1,a1), App(h2,a2) ->
        begin match observe h1, observe h2 with
          | Var v1, _ when variable v1.tag ->
            let (res, a1') = check_flex_args (List.map hnorm a1) v1.ts in
            if res
            then 
              unify_app_term tyctx h1 a1' t1 t2
            else
              unify_app_term tyctx h1 a1 t1 t2 
          | _, Var v2 when variable v2.tag ->
            let (res, a2') = check_flex_args (List.map hnorm a2) v2.ts in
            if res
            then 
              unify_app_term tyctx h2 a2' t2 t1
            else
              unify_app_term tyctx h1 a1 t1 t2 
          | _ -> unify_app_term tyctx h1 a1 t1 t2
        end
    | App (h1,a1),_                 -> unify_app_term tyctx h1 a1 t1 t2
    | _,App (h2,a2)                 -> unify_app_term tyctx h2 a2 t2 t1
    | DB i1,DB i2 -> if i1 <> i2 then fail (ConstClash(t1, t2))
    | Var c1,_ when constant c1.tag -> unify_const_term tyctx t1 t2
    | _,Var c2 when constant c2.tag -> unify_const_term tyctx t2 t1
    | _ -> failwith "logic variable on the left (7)"
  with
    | UnifyError NotLLambda ->
        let n = max (closing_depth t1) (closing_depth t2) in
        let tys = List.rev (List.take n tyctx) in
          handler (lambda tys t1) (lambda tys t2)

let pattern_unify ~used t1 t2 =
  local_used := used ;
  unify [] (hnorm t1) (hnorm t2)  
        
(* Given Lam(tys1, App(h1, a1)) and Lam(tys2, App(h2, a2))
   where h1 is flexible, h2 is rigid, and len(tys1) <= len(tys2),
   return a complete list of possible bindings for h1 *)
let flexible_heads ~used (tys1, h1, a1) (tys2, h2, a2) =
  assert (tc [] (lambda tys1 (app h1 a1)) = tc [] (lambda tys2 (app h2 a2))) ;
  let n1 = List.length tys1 in
  let n2 = List.length tys2 in
  let () = assert (n2 >= n1) in
  let tys2' = List.drop n1 tys2 in
  let a1tys = List.map (tc (List.rev tys1)) a1 in
  let a1ids = gen_binder_ids (List.length a1) in
  let a1ctx = List.combine a1ids a1tys in
  let a2tys = List.map (tc (List.rev tys2)) a2 in
  let a1n = List.length a1 in
  let hv1 = term_to_var h1 in
  let () = assert (variable hv1.tag) in

  let create_raised_vars arg_tys target_tys =
    local_used := used ;
    let dbs = List.rev_map db (List.range 1 (List.length arg_tys)) in
      List.map
        (fun ty ->
           let arg_tys, dbs =
             List.split
               (List.filter
                  (* We aren't implementing subordination so behave as if all types are subordinate *)
                  (* (fun (aty, _) -> Subordination.query sr aty ty) *)
                  (fun _ -> true)
                  (List.combine arg_tys dbs))
           in
           app (named_fresh  hv1.name
                            hv1.ts (Type.tyarrow arg_tys ty)) dbs)
        target_tys
  in

  (* Imitation *)
  let imitable =
    match observe (hnorm h2) with
      | Var v when constant v.tag -> true
      | DB i -> i <= n2 - n1
      | _ -> assert false
  in
  let imitation =
    if imitable then
      [lambda (a1ctx @ tys2')
         (app h2 (create_raised_vars (a1tys @ (get_ctx_tys tys2')) a2tys))]
    else
      []
  in

  (* Projection *)
  let projections =
    let n = a1n + (n2 - n1) in
    let bty = match hv1.ty with Type.Ty(tys, ty) -> Type.Ty(List.drop n tys, ty) in
    let bn = match bty with Type.Ty(tys, _) -> List.length tys in
      List.filter_map
        (fun (_, aty, i) ->
           let Type.Ty(tys, ty) = aty in
           let use = List.drop_last bn tys in
           let leave = List.take_last bn tys in
             if Type.Ty(leave, ty) = bty then
               Some
                 (lambda (a1ctx @ tys2')
                    (app (db (n-i))
                       (create_raised_vars (a1tys @ (get_ctx_tys tys2')) use)))
             else
               None)
        (List.combine3 a1 a1tys (List.range 0 (a1n - 1)))
  in

  (* Final results *)
  let results = imitation @ projections in
  let () =
    let tyctx = List.rev tys1 in
      List.iter (fun r -> assert (hv1.ty = tc tyctx r)) results
  in
    results

end

let standard_handler _ _ = raise (UnifyError NotLLambda)

module Right =
  Make (struct
          let instantiatable = Logic
          let constant_like = Eigen
          let handler = standard_handler
        end)
  
module Left =
  Make (struct
          let instantiatable = Eigen
          let constant_like = Logic
          let handler = standard_handler
        end)

let right_unify ?used:(used=[]) t1 t2 =
  Right.pattern_unify ~used t1 t2
    
let left_unify ?used:(used=[]) t1 t2 =
  Left.pattern_unify ~used t1 t2
    
let try_with_state ~fail f =
  let state = get_scoped_bind_state () in
    try
      f ()
    with
      | UnifyFailure _ | UnifyError _ -> set_scoped_bind_state state ; fail

let try_right_unify ?used:(used=[]) t1 t2 =
  try_with_state ~fail:false
    (fun () ->
       right_unify ~used t1 t2 ;
       true)

let try_right_unify_cpairs t1 t2 =
  try_with_state ~fail:None
    (fun () ->
       let cpairs = ref [] in
       let cpairs_handler x y = cpairs := (x,y)::!cpairs in
       let module RightCpairs =
         Make (struct
                 let instantiatable = Logic
                 let constant_like = Eigen
                 let handler = cpairs_handler
               end)
       in
         RightCpairs.pattern_unify ~used:[] t1 t2 ;
         Some !cpairs)
    
let try_left_unify_cpairs ~used t1 t2 =
  let state = get_scoped_bind_state () in
  let cpairs = ref [] in
  let cpairs_handler x y = cpairs := (x,y)::!cpairs in
  let module LeftCpairs =
    Make (struct
            let instantiatable = Eigen
            let constant_like = Logic
            let handler = cpairs_handler
          end)
  in
    try
      LeftCpairs.pattern_unify ~used t1 t2 ;
      Some !cpairs
    with
      | UnifyFailure _ -> set_scoped_bind_state state ; None
      | UnifyError _ -> set_scoped_bind_state state ;
          failwith "Unification error during case analysis"

(* Given two lists of terms, unify corresponding elements
 * of the two lists.
 * Assumes that the given lists are of the same length,
 * that all the terms are well formed.*)            
let try_left_unify_list_cpairs ~used l1 l2 =
  let state = get_scoped_bind_state () in
  let cpairs = ref [] in
  let cpairs_handler x y = cpairs := (x,y)::!cpairs in
  let module LeftCpairs =
    Make (struct
            let instantiatable = Eigen
            let constant_like = Logic
            let handler = cpairs_handler
          end)
  in
    try
      List.iter2 (LeftCpairs.pattern_unify ~used) l1 l2 ;
      Some !cpairs
    with
      | UnifyFailure _
      | Invalid_argument _ -> set_scoped_bind_state state ; None
      | UnifyError _ -> set_scoped_bind_state state ;
          failwith "Unification error during case analysis"
