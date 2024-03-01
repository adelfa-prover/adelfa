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

(** [block_sim f ctx_var sub_rel b1 b2] checks if the block [b1] is similar to
    the block [b2] with respect to [sub_rel], [f], and [ctx_var].

    This is done by descending the formula [f] and checking if the blocks are
    equal modulo subordination for every atomic formula qualified by [ctx_var]
    and only [ctx_var]. *)
val block_sim
  :  formula
  -> Context.ctx_var
  -> Subordination.sub_rel
  -> Context.block_schema
  -> Context.block_schema
  -> bool

(** [block_in_schema_sub f ctx_var sub_rel b c] checks if the block [b] is in
    the schema [c] with respect to [sub_rel], [f], and [ctx_var]. *)
val block_in_schema_sub
  :  formula
  -> Context.ctx_var
  -> Subordination.sub_rel
  -> Context.block_schema
  -> Context.ctx_schema
  -> bool

(** [schema_transports f ctx_var sub_rel c1 c2] checks if [ctx_var] in a formula
    [f] can be transported from a context schema [c1] to a context schema [c2]
    with respect to [sub_rel]. *)
val schema_transports
  :  formula
  -> Context.ctx_var
  -> Subordination.sub_rel
  -> Context.ctx_schema
  -> Context.ctx_schema
  -> bool

(** [get_compatible_context_schemas ctx_schemas sub_rel f] returns a list of
    pairs [(v, ys)] where [v] is a context variable and [ys] is a list of
    context schemas which [v] is compatible with. *)
val get_compatible_context_schemas
  :  (Context.ctx_var * Context.ctx_schema) list
  -> Subordination.sub_rel
  -> formula
  -> (Context.ctx_var * Context.schema_name list) list

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
