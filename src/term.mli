(**TERM
   * Representation of the terms of the logic.
   *
   * These terms represent LF expressions and can be viewed as
   * simply-typed terms in a weakly typed setting or as
   * dependently-typed terms in an LF setting. *)

open Type

(** [tag] The different types of variables of LF *)
type tag =
  | Eigen
  | Constant
  | Logic
  | Nominal

(** [id] The string identifier for a {!type:var} *)
type id = string

(* Note about timestamps: Constants from sig are all at the outtermost level, ts = 0 Then
   are all the eigenvariables, ts = 1 Then there are the bound variables, ts = 2 Finally,
   nominals are also at the same as bound vars, ts = 2*)

(** [var] An LF variable *)
type var =
  { name : id (** [name] The string representation of [var] *)
  ; tag : tag (** [tag] Represents what type of [var] this is *)
  ; ts : int (** [ts] A timestamp to support restrictions in unification easier *)
  ; ty : ty (** [ty] The {!type:Type.ty} of the variable *)
  }

type t = var

val compare : t -> t -> int

(** [term] an LF term *)
type term =
  | Var of var
  | DB of int
  | Lam of tyctx * term
  | App of term * term list
  | Susp of term * int * int * env
  | Ptr of ptr
  (* New term constructors *)
  | Pi of lftyctx * term
  | Type

(* type contexts for abstractions identify arity types, and type contexts for pis identify
   LF types for bound variables. *)
and tyctx = (id * ty) list
and lftyctx = (var * term) list
and env = envitem list

and envitem =
  | Dum of int
  | Binding of term * int

and ptr = in_ptr ref

and in_ptr =
  | V of var
  | T of term

val lftyctx_to_tyctx : lftyctx -> tyctx
val observe : term -> term
val rename_vars : (id * id) list -> term -> term
val db : int -> term
val get_ctx_tys : tyctx -> Type.ty list
val get_lfctx_tys : lftyctx -> term list
val lambda : tyctx -> term -> term
val abstract : id -> ty -> term -> term
val app : term -> term list -> term
val susp : term -> int -> int -> env -> term
val pi : lftyctx -> term -> term
val get_ty_head : term -> id
val is_kind : term -> bool
val hnorm : term -> term
val norm : term -> term
val eta_normalize : term -> term
val eq : term -> term -> bool

type bind_state

val bind_state : bind_state ref
val bind : term -> term -> unit
val get_bind_state : unit -> bind_state
val set_bind_state : bind_state -> unit

type scoped_bind_state = int

val get_scoped_bind_state : unit -> int
val set_scoped_bind_state : int -> unit
val unwind_state : ('a -> 'b) -> 'a -> 'b
val nominal_var : id -> ty -> term
val var : tag -> id -> int -> ty -> term

(* only use to get the name/id of var terms *)
val get_id : term -> id
val get_tag : term -> tag
val get_var_ty : term -> ty
val is_var : tag -> term -> bool
val const : ?ts:int -> id -> ty -> term
val logic : ?ts:int -> id -> ty -> term
val find_vars : tag -> term list -> var list
val find_var_refs : tag -> term list -> term list

module Notations : sig
  val ( // ) : tyctx -> term -> term
  val ( ^^ ) : term -> term list -> term
end

val reset_varcount : unit -> unit
val get_varcount : unit -> int
val set_varcount : int -> unit
val fresh : ?tag:tag -> ?ts:int -> Type.ty -> term

val fresh_wrt
  :  ts:int
  -> tag
  -> string
  -> ty
  -> (id * term) list
  -> term * (id * term) list

val term_to_name : term -> id
val term_to_pair : term -> id * term
val term_to_var : term -> var
val var_to_term : var -> term
val replace_term_vars : ?tag:tag -> (id * term) list -> term -> term
val get_used : term list -> (id * term) list
val convert_to_nominals : lftyctx -> (id * term) list -> term list
val tc : tyctx -> term -> Type.ty
val erase : term -> Type.ty
val eta_expand : term -> term
val is_uninstantiated : id * term -> bool
val alpha_eq : term -> term -> (id * id) list -> (id * id) list option
