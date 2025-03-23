(*
 *
 * SEQUENT
 * Representation of a sequent/subgoal.
 * 
 *
 *)

type tag =
  | Explicit
  | Implicit

type hyp =
  { id : string
  ; tag : tag
  ; formula : Formula.formula
  }

type sequent =
  { mutable vars : (string * Term.term) list
  ; mutable ctxvars : Context.CtxVarCtx.t
  ; mutable hyps : hyp list
  ; mutable goal : Formula.formula
  ; mutable count : int
  ; mutable name : string
  ; mutable next_subgoal_id : int
  }

val cp_sequent : sequent -> sequent
val assign_sequent : sequent -> sequent -> unit
val add_var : sequent -> Term.id * Term.term -> unit
val remove_var : sequent -> Term.id -> unit
val add_if_new_var : sequent -> Term.id * Term.term -> unit
val get_nominals : sequent -> (Term.id * Term.term) list
val get_eigen : sequent -> (Term.id * Term.term) list

val add_ctxvar
  :  sequent
  -> Context.ctx_var
  -> ?rstrct:Term.var list
  -> Context.ctx_typ
  -> unit

val remove_ctxvar : sequent -> Context.ctx_var -> unit

val replace_assoc_ctxvars_restricted
  :  (Term.id * Term.term) list
  -> (Context.ctx_var * Term.id list) list
  -> (Context.ctx_var * Term.id list) list

(* Raises Not_found if the given context variable is not in the context *)
val fresh_hyp_name : sequent -> string -> string
val add_hyp : sequent -> ?name:string -> Formula.formula -> unit
val make_hyp : sequent -> ?name:string -> ?tag:tag -> Formula.formula -> hyp
val get_hyp : sequent -> string -> hyp
val remove_hyp : sequent -> string -> unit
val replace_hyp : sequent -> string -> Formula.formula -> unit
val norm_atom : sequent -> Formula.formula -> Formula.formula
val prune_noms : sequent -> unit
val exists_left : sequent -> Formula.formula -> Formula.formula
val norm : sequent -> Formula.formula -> Formula.formula
val normalize_formula : sequent -> string -> Formula.formula -> unit
val normalize_hyps : sequent -> unit
val make_sequent_from_goal : ?name:string -> form:Formula.formula -> unit -> sequent
val replace_seq_vars : (Term.id * Term.term) list -> sequent -> unit
val eq : sequent -> sequent -> bool

module Print : sig
  val pr_str : Format.formatter -> string -> unit
  val pr_hyp : Format.formatter -> hyp -> unit
  val pr_hyps : Format.formatter -> hyp list -> unit
  val pr_sequent : Format.formatter -> sequent -> unit
  val string_of_sequent : sequent -> string
end
