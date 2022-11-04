(* UNIFY
 * Pattern unification of terms.
 *)

open Term

type unify_failure =
  | OccursCheck
  | ConstClash of (term * term)
  | Generic
  | FailTrail of int * unify_failure
  | MatchingFormula of Formula.formula

exception UnifyFailure of unify_failure

val explain_failure : unify_failure -> string
val right_unify : ?used:(id * term) list -> term -> term -> unit
val left_unify : ?used:(id * term) list -> term -> term -> unit
val try_right_unify : ?used:(id * term) list -> term -> term -> bool
val try_right_unify_cpairs : term -> term -> (term * term) list option

val try_left_unify_cpairs
  :  used:(id * term) list
  -> term
  -> term
  -> (term * term) list option

val try_left_unify_list_cpairs
  :  used:(id * term) list
  -> term list
  -> term list
  -> (term * term) list option
