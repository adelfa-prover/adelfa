(*
 *
 * Signature
 * Representation of LF Signature declarations.
 * 
 *)

type id = string

type associativity =
  | None
  | Right
  | Left

type fixity =
  | Infix of associativity * int
  | Prefix of int
  | Postfix of int
  | NoFixity

type type_decl =
  { ty_name : id
  ; kind : Term.term
  ; ty_implicit : int
  ; ty_fix : fixity
  ; mutable objs : id list
  }

and obj_decl =
  { obj_name : id
  ; typ : Term.term
  ; obj_implicit : int
  ; obj_fix : fixity
  }

val ty_dec : id -> Term.term -> int -> fixity -> id list -> type_decl
val obj_dec : id -> Term.term -> int -> fixity -> obj_decl

type signature

val empty : signature
val get_type_decls : signature -> type_decl list
val get_obj_decls : signature -> obj_decl list
val add_type_decl : signature -> type_decl -> signature
val is_type : signature -> id -> bool
val lookup_type_decl_op : signature -> id -> type_decl option
val lookup_type_decl : signature -> id -> type_decl
val add_obj_decl : signature -> obj_decl -> signature
val is_obj : signature -> id -> bool
val lookup_obj_decl_op : signature -> id -> obj_decl option
val lookup_obj_decl : signature -> id -> obj_decl
