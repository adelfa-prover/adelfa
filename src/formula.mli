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

val collect_vars_ctx : formula -> Term.var list
val collect_terms : CtxVarCtx.t -> formula -> term list
val replace_formula_vars : (id * term) list -> formula -> formula

val replace_formula_vars_rename
  :  used:(id * term) list
  -> (id * term) list
  -> formula
  -> formula

val block_sim
  :  formula
  -> Context.ctx_var
  -> Subordination.sub_rel
  -> Context.block_schema
  -> Context.block_schema
  -> bool

val block_in_schema_sub
  :  formula
  -> Context.ctx_var
  -> Subordination.sub_rel
  -> Context.block_schema
  -> Context.ctx_schema
  -> bool

val schema_transports
  :  formula
  -> Context.ctx_var
  -> Subordination.sub_rel
  -> Context.ctx_schema
  -> Context.ctx_schema
  -> bool

val reduce_inductive_annotation : annotation -> annotation
val formula_to_annotation : formula -> annotation
val copy_formula : formula -> formula
val norm : formula -> formula
val eta_expand : formula -> formula
val replace_ctx_vars : (Context.ctx_var * Context.ctx_expr) list -> formula -> formula
val get_formula_used_ctxvars : formula -> Context.ctx_var list
val get_formula_ctx_opt : formula -> Context.ctx_expr option
val get_ctx_var_opt : formula -> Context.ctx_var option
val context_support : CtxVarCtx.t -> Context.ctx_expr -> term list
val context_support_sans : CtxVarCtx.t -> Context.ctx_expr -> term list
val formula_support : CtxVarCtx.t -> formula -> term list
val get_formula_used : CtxVarCtx.t -> formula -> (id * term) list
val get_formula_used_nominals : CtxVarCtx.t -> formula -> (id * term) list
val formula_support_sans : CtxVarCtx.t -> formula -> term list
