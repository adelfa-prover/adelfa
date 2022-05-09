(* Module for translation of untyped expressions into (arity) typed expressions *)

type typing_error =
  | NoType of Uterms.pos * Term.id
  | TypeMismatch of Uterms.pos * Type.ty * Type.ty
  | TooManyArgs of Uterms.pos
  | BadSchema of Uterms.pos * string
  | BadDefinition of Uterms.pos * Term.id
  | BadProp of Uterms.pos
  | UnknownContext of Uterms.pos * Context.ctx_var
  | UnknownConstant of Uterms.pos * Term.id
  | Other of Uterms.pos * string

exception TypingError of typing_error

val notype : Uterms.pos -> Term.id -> typing_error
val typemismatch : Uterms.pos -> Type.ty -> Type.ty -> typing_error
val badschema : Uterms.pos -> string -> typing_error
val baddefinition : Uterms.pos -> string -> typing_error
val badprop : Uterms.pos -> typing_error
val unknowncontext : Uterms.pos -> Context.ctx_var -> typing_error
val unknownconstant : Uterms.pos -> Term.id -> typing_error
val other : Uterms.pos -> string -> typing_error
val get_error_pos : typing_error -> Uterms.pos
val explain_error : typing_error -> string

val trans_term
  :  Signature.signature
  -> (Term.id * Term.term option ref) list
  -> (Term.id * Term.term option ref) list
  -> (Term.id * Term.term option ref) list
  -> (Term.id * Term.term option ref) list
  -> Type.ty option
  -> Uterms.uterm
  -> Term.term * (Term.id * Term.term option ref) list

val trans_formula
  :  Signature.signature
  -> (string * Context.ctx_schema) list
  -> (string * Type.ty) list
  -> (Term.id * Term.term option ref) list
  -> (Term.id * Term.term option ref) list
  -> Sequent.cvar_entry list
  -> (Term.id * Term.term option ref) list
  -> Uterms.uformula
  -> Formula.formula

val trans_ctx
  :  Signature.signature
  -> (Term.id * Term.term option ref) list
  -> (Term.id * Term.term option ref) list
  -> Sequent.cvar_entry list
  -> (Term.id * Term.term option ref) list
  -> Uterms.uctx
  -> Context.ctx_expr * (Term.id * Term.term option ref) list

val trans_schema : Signature.signature -> Uterms.uschema -> Context.ctx_schema

val trans_dfn
  :  Signature.signature
  -> (string * Context.ctx_schema) list
  -> (string * Type.ty) list
  -> Term.id
  -> Type.ty
  -> Uterms.udef list
  -> Definition.dfn
