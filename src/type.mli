(*
 * TYPE
 * Representation of arity types.
 * 
 * This file defines the representation of arity types which is
 * the typing used in the logic.
 *)

type ty = Ty of ty list * string

val tyarrow : ty list -> ty -> ty
val tybase : string -> ty
val eq : ty -> ty -> bool
val oty : ty
val propty : ty

module Print : sig
  val pr_str : Format.formatter -> string -> unit
  val pr_ty_literal : Format.formatter -> ty -> unit
  val pr_tylst_literal : Format.formatter -> ty list -> unit
  val string_of_ty_literal : ty -> string
  val pr_ty : Format.formatter -> ty -> unit
  val string_of_ty : ty -> string
end
