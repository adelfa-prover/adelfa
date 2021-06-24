open Term
open Type

(* Lf type checking *)
val wf_ctx : Signature.signature -> lftyctx -> unit
val get_type : Signature.signature -> lftyctx -> term -> term
val check_type : Signature.signature -> lftyctx -> term -> term -> term

(* Context Expression Typing *)
val of_schema : (Term.id * Term.term) list ->
  (Context.ctx_var * Context.ctx_typ) list ->
  Context.ctx_expr ->
  (id * Context.ctx_schema) -> bool

(* Arity type checking for processed terms.*)
exception TypeError of ty * ty
val infer_ty : ty list -> term -> ty
val of_type : term -> ty -> bool
