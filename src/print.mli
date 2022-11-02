(* These general printing functions do not make use of fixity or 
   implicit information from the signature *)

val pr_ty : Format.formatter -> Type.ty -> unit
val pr_term : Term.id list -> Format.formatter -> Term.term -> unit
val pr_formula : Format.formatter -> Formula.formula -> unit
val pr_ctxexpr : Format.formatter -> Context.ctx_expr -> unit
val pr_sequent : Format.formatter -> Sequent.sequent -> unit
val pr_uterm : Format.formatter -> Uterms.uterm -> unit
val print_ty : Type.ty -> unit
val print_term : Term.term -> unit
val print_sequent : Sequent.sequent -> unit
val print_uterm : Uterms.uterm -> unit
val string_of_ty_literal : Type.ty -> string
val string_of_term_literal : Term.term -> string
val string_of_formula : Formula.formula -> string
val string_of_ty : Type.ty -> string
val string_of_term : Term.term -> string
val string_of_sequent : Sequent.sequent -> string
val string_of_ctxexpr : Context.ctx_expr -> string
val string_of_uterm : Uterms.uterm -> string
val string_of_uform : Uterms.uformula -> string
val string_of_command : Uterms.command -> string
val string_of_topcommand : Uterms.top_command -> string
val string_of_subst : (Term.id * Term.term) list -> string
val string_of_ctxvarty : Context.ctx_typ -> string
