(*
 * TACTICS
 * Implement tactics for reasoning.
 *
 *)

exception InvalidFormula of Formula.formula * string
exception InvalidTerm of Term.term
exception InvalidName of string
exception NotLlambda
exception NoCases
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

val make_case : Sequent.sequent -> case

(* Given a sequent, searches for derivation using id, atm-R, pi-R,
 * base-R, top-R, and bottom-L rules. 
 * Raises Success upon finding a derivarion.
 *)
val search : depth:int -> Signature.signature -> Sequent.sequent -> unit

(* Given a sequent and an integer identifying which subformula to
 * induct on, returns an updated sequent with annotations added and
 * inductive hypothesis in the assumptions.
 * Raises InvalidFormula if the identified subformula is not atomic.
 *)
val reset_ind_count : unit -> unit
val ind : Sequent.sequent -> int -> unit

(* Given a sequent and a name identifying an assumption formula,
 * of the sequent this will perform case analysis on the 
 * identified subgoal and will return the updated sequent and list
 * of new subgoals if any.
 * Raises InvalidFormula if the identified assumption is not atomic.
 * Raises NotLlambda if unification cannot be completed.
 *)
val cases
  :  Signature.signature
  -> (string * Context.ctx_schema) list
  -> Sequent.sequent
  -> string
  -> case list

(* Given a sequent and a term, checks that the term is weakly well
 * formed of the appropriate weak type and then instantiates the
 * goal formula with that term and returns the updated sequent.
 * Raises InvalidTerm if the term is not weakly well typed.
 *)
val exists : Sequent.sequent -> Term.term -> unit

(* Given a sequent, a formula, and a list of hyp names
 * will apply the formula to the given hypotheses (inferring
 * instantiations for universal and context quantifiers)
 * and adds the resulting formula to the sequent. *)
val apply
  :  (string * Context.ctx_schema) list
  -> Sequent.sequent
  -> Formula.formula
  -> Formula.formula list
  -> Formula.formula

val apply_with
  :  (string * Context.ctx_schema) list
  -> Sequent.sequent
  -> Formula.formula
  -> Formula.formula list
  -> (Term.id * Term.term) list * (Context.ctx_var * Context.ctx_expr) list
  -> Formula.formula

(* (\* Given a sequent, applies one of:  ctx-R, all-R, and imp-R and  *)
(*  * returns the resulting sequent. *\) *)
val intro : Sequent.sequent -> unit

(* (\* Like intro but applies all ctx-R, all-R, and imp-R possible to the  *)
(*  * given sequent. *\) *)
val intros : Sequent.sequent -> unit
val split : Formula.formula -> Formula.formula * Formula.formula
val left : Formula.formula -> Formula.formula
val right : Formula.formula -> Formula.formula

val weaken
  :  depth:int
  -> Signature.signature
  -> Sequent.sequent
  -> Formula.formula
  -> Term.term
  -> unit

exception InvalidCtxPermutation of string

(* Checks if the permutation of the context is valid,
   returns modified formula with permuted context
   raises InvalidCtxPermutation if given context expression is not
   as good permutation. *)
val permute_ctx : Formula.formula -> Context.ctx_expr -> Formula.formula
val strengthen : Sequent.cvar_entry list -> Formula.formula -> Formula.formula option

exception InstTypeError of Formula.formula

val inst
  :  depth:int
  -> Signature.signature
  -> Sequent.sequent
  -> Formula.formula
  -> (Term.id * Term.term) list
  -> Formula.formula

val prune : Sequent.sequent -> Formula.formula -> unit
