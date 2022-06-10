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

type cvar_entry = Context.ctx_var * Term.id list ref * Context.ctx_typ

type sequent =
  { mutable vars : (Term.id * Term.term) list
  ; mutable ctxvars : cvar_entry list
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
  -> ?rstrct:Term.id list
  -> Context.ctx_typ
  -> unit

val remove_ctxvar : sequent -> Context.ctx_var -> unit
val get_ctxvar_id : cvar_entry -> string
val get_ctxvar_restricted : cvar_entry -> Term.id list
val get_ctxvar_ty : cvar_entry -> Context.ctx_typ
val restrict_in : cvar_entry -> Term.id list -> cvar_entry
val ctxvar_mem : cvar_entry list -> Context.ctx_var -> bool

(* Raises Not_found if the given context variable is not in the context *)
val ctxvar_lookup : cvar_entry list -> Context.ctx_var -> cvar_entry
val get_cvar_tys : cvar_entry list -> (Context.ctx_var * Context.ctx_typ) list
val fresh_hyp_name : sequent -> string -> string
val add_hyp : sequent -> ?name:string -> Formula.formula -> unit
val make_hyp : sequent -> ?name:string -> ?tag:tag -> Formula.formula -> hyp
val get_hyp : sequent -> string -> hyp
val remove_hyp : sequent -> string -> unit
val replace_hyp : sequent -> string -> Formula.formula -> unit
val norm_atom : sequent -> Formula.formula -> Formula.formula
val exists_left : sequent -> Formula.formula -> Formula.formula
val norm : sequent -> Formula.formula -> Formula.formula
val normalize_formula : sequent -> string -> Formula.formula -> unit
val normalize_hyps : sequent -> unit
val make_sequent_from_goal : ?name:string -> form:Formula.formula -> unit -> sequent
val replace_seq_vars : (Term.id * Term.term) list -> sequent -> unit
