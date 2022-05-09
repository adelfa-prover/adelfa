(*
 *
 * FORMULA
 * Representation of the Formulas of the logic.
 *
 *)
open Term
open Context

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
  | Prop of Term.id * Term.term list

val eq : formula -> formula -> bool

(* Constructions *)
val atm : ?ann:annotation -> ctx_expr -> term -> term -> formula
val imp : formula -> formula -> formula
val f_and : formula -> formula -> formula
val f_or : formula -> formula -> formula
val forall : tyctx -> formula -> formula
val exists : tyctx -> formula -> formula
val ctx : (id * id) list -> formula -> formula
val prop : id -> Term.term list -> formula
val map_terms : (term -> term) -> formula -> formula

val fresh_alist
  :  used:(id * term) list
  -> tag:Term.tag
  -> ts:int
  -> (Term.id * Type.ty) list
  -> (Term.id * term) list

val raise_type : term list -> Type.ty -> Type.ty

val fresh_raised_alist
  :  used:(id * term) list
  -> tag:Term.tag
  -> ts:int
  -> support:term list
  -> (Term.id * Type.ty) list
  -> (id * term) list * term list

val collect_terms : (Context.ctx_var * Context.ctx_typ) list -> formula -> term list
val replace_formula_vars : (id * term) list -> formula -> formula

val replace_formula_vars_rename
  :  used:(id * term) list
  -> (id * term) list
  -> formula
  -> formula

val reduce_inductive_annotation : annotation -> annotation
val formula_to_annotation : formula -> annotation
val copy_formula : formula -> formula
val norm : formula -> formula
val replace_ctx_vars : (Context.ctx_var * Context.ctx_expr) list -> formula -> formula
val get_formula_used_ctxvars : formula -> Context.ctx_var list

val context_support
  :  (Context.ctx_var * Context.ctx_typ) list
  -> Context.ctx_expr
  -> term list

val context_support_sans
  :  (Context.ctx_var * Context.ctx_typ) list
  -> Context.ctx_expr
  -> term list

val formula_support : (Context.ctx_var * Context.ctx_typ) list -> formula -> term list

val get_formula_used
  :  (Context.ctx_var * Context.ctx_typ) list
  -> formula
  -> (id * term) list

val get_formula_used_nominals
  :  (Context.ctx_var * Context.ctx_typ) list
  -> formula
  -> (id * term) list

val formula_support_sans
  :  (Context.ctx_var * Context.ctx_typ) list
  -> formula
  -> term list
