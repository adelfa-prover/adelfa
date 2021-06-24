(*
 * TYPE
 * Representation of arity types.
 * 
 * This file defines the representation of arity types which is
 * the typing used in the logic.
 *) 

type ty =
  | Ty of ty list * string

val tyarrow : ty list -> ty -> ty
val tybase : string -> ty
val eq : ty -> ty -> bool
  
val oty : ty
val propty : ty
