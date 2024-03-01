(** [Context] is a representation of context expressions *)

(** [ctx_var] represents implicit portion of context expression. *)
type ctx_var = string

(** [entry] is a variable with an associated type *)
type entry = Term.var * Term.term

(** [ctx_expr] represents contexts of typing judgements *)
type ctx_expr =
  | Nil (** [Nil] represents empty context*)
  | Var of ctx_var (** [Var s] represents implicit portion identified by [s]*)
  | Ctx of ctx_expr * entry
  (** [Ctx expr entry] adds an explicit portion to the context *)

(** [entry_eq e1 e2] determines if an entry in an explicit portion of
    the context has the same identifier and are of the same type.*)
val entry_eq : entry -> entry -> bool

(** [eq g1 g2] determines if two context expressions are equivalent.

    Equivalence requires the same context variable name as well as
    the same explicit portion.*)
val eq : ctx_expr -> ctx_expr -> bool

(** [ctx_var s] creates a [ctx_var] from a string identifier *)
val ctx_var : string -> ctx_var

(** [ctx_var_eq v1 v2] checks if two contexts variables are equivalent *)
val ctx_var_eq : ctx_var -> ctx_var -> bool

(** [append_context ctx es] adds explicit portion [es] to the end of the context [ctx] *)
val append_context : ctx_expr -> entry list -> ctx_expr

(** [context_map f c] applies [f] to each entry in [c] *)
val context_map : (Term.term -> Term.term) -> ctx_expr -> ctx_expr

(** [replace_ctx_expr_vars ?tag alist ctx] returns a new context in which
    terms in the context have substitutions in [alist] carried out *)
val replace_ctx_expr_vars
  :  ?tag:Term.tag
  -> (string * Term.term) list
  -> ctx_expr
  -> ctx_expr

(** [reset_varcount] sets internal variable counter to 1 *)
val reset_varcount : unit -> unit

(** [get_varcount] returns the amount of variables used *)
val get_varcount : unit -> int

(** [set_varcount i] adjusts internal variable counter to [i] *)
val set_varcount : int -> unit

(** [fresh_wrt name used] gives a numbered version of [name] such that it
    does not appear in [used] *)
val fresh_wrt : string -> ctx_var list -> ctx_var * ctx_var list

(** [fresh_wrt name used] gives a numbered version of [name] such that it
    does not appear in [used] *)
val list_fresh_wrt
  :  (ctx_var * string) list
  -> ctx_var list
  -> (ctx_var * ctx_var * string) list * ctx_var list

(** [has_var g] determines if there is a context variable in the given
    context expression. *)
val has_var : ctx_expr -> bool

(** [get_ctx_var g] returns the context variable representing the implicit
    portion. Raises [Invalid_argument] if there is no implicit portion in
    the context expression. *)
val get_ctx_var : ctx_expr -> ctx_var

(** [get_ctx_var_opt g] returns [Some v] where is the context variable
    representing the implicit portion. Gives [None] if there is no implicit
    portion in the context expression. *)
val get_ctx_var_opt : ctx_expr -> ctx_var option

(** [get_used_ctxvars gs] gives a list of unique context variables in [gs] *)
val get_used_ctxvars : ctx_expr list -> ctx_var list

(* context types *)

(** [block] are context blocks ordered from earliest in the context to latest. *)
type block = entry list

(** [ctx_typ] *)
type ctx_typ = CtxTy of string * block list

val ctx_typ : ?blocks:block list -> id:string -> unit -> ctx_typ

(**[replace_ctx_typ_vars ?tag alist ty] applies the substitutions in [alist]
   within the given context type's blocks *)
val replace_ctx_typ_vars
  :  ?tag:Term.tag
  -> (string * Term.term) list
  -> ctx_typ
  -> ctx_typ

(* context schemas *)

(** [wctx] is a list of types associated with arities in a schema *)
type wctx = (Term.id * Type.ty) list

(** [block_schema] represents a block schema in a context.

    A tuple where the first element represents the header variables with arity types
    and the second element represents the schematic variables *)
type block_schema = B of wctx * entry list

(** [schema_name] represents an identifier for a [ctx_schema] *)
type schema_name = string

(** [ctx_schema] is a context schema [block_schema] *)
type ctx_schema = block_schema list

module CtxVarCtx : sig
  (** Context variable context for a sequent. *)
  module H = Extensions.Hashtbl

  module Res = VarSet

  (** The type of the context variables *)
  type v = ctx_var

  type ctx_ty = ctx_typ
  type d = Res.t ref * ctx_ty
  type entry = v * d

  (** The context varaible context type *)
  type t

  (** [empty ()] creates a new empty context variable context *)
  val empty : unit -> t

  (** [is_empty ctx] determines if there are no entries in the context. *)
  val is_empty : t -> bool

  (** [add_var ctx var ?res ctx_ty] adds [var] to the context var context with a
      new restricted set which contains all elements in [res] and has the schema
      and blocks given in [ctx_ty] *)
  val add_var : t -> v -> ?res:Res.elem list -> ctx_ty -> unit

  (** [add_vars ctx vars] takes a list of key value pairs from a context
      variable context and inserts them into [ctx] *)
  val add_vars : t -> (v * d) list -> unit

  (** [to_list ctx] gives a list of key value pairs from [ctx]*)
  val to_list : t -> (v * d) list

  (** [of_list entries] takes a list of key values pairs a returns a new ctx var
      ctx representing it *)
  val of_list : (v * d) list -> t

  (** [of_list_list entries] takes a list of context variables and entries but
      instead of a [VarSet] for the restricted set, the function will create it
      for the caller. *)
  val of_list_list : (v * (Res.elem list * ctx_ty)) list -> t

  (** [get_vars ctx] returns all context variables in the context *)
  val get_vars : t -> v list

  (** [find_var_opt ctx var] returns [Some] value if [var] is in the context,
      otherwise [None] *)
  val find_var_opt : t -> v -> d option

  (** [find_var_opt ctx var] returns [var]'s value if [var] is in the context,
      otherwise raises [Not_found] *)
  val find : t -> v -> d

  (** [mem ctx var] determines if [var] has an entry in [ctx] *)
  val mem : t -> v -> bool

  (** [restrict_in ctx var elems] adds all of the elements of [elems] to the
      restricted set of [var] *)
  val restrict_in : t -> v -> Res.elem list -> unit

  (** [remove_var ctx var] removes [var] from [ctx]*)
  val remove_var : t -> v -> unit

  (** [copy ctx] returns a deep copy of [ctx] *)
  val copy : t -> t

  (** [get_var_schema ctx var] returns [Some] schema which quantifies [var] or
      [None] if [var] is not present in [ctx] *)
  val get_var_schema : t -> v -> string option

  (** [get_var_tys ctx] returns all of the context vars in [ctx] along with
      their type *)
  val get_var_tys : t -> (v * ctx_ty) list

  (** [get_var_blocks ctx var] returns the elaborated context blocks
      corresponding to [var] *)
  val get_var_blocks : t -> v -> block list

  (** [get_var_restricted ctx var] gives the restricted set corresponding to
      [var] or [None] if [var] is not present in [ctx]*)
  val get_var_restricted : t -> v -> Res.t option

  (** [remove_all f ctx] will remove all entries from [ctx] which satisfy [f] *)
  val remove_all : (v -> d -> bool) -> t -> unit

  (** [map_inplace f ctx] will apply [f] to all entries of [ctx] modifying it inplace *)
  val map_inplace : (v -> d -> d) -> t -> unit

  (** [map_entries f ctx] retuns a list of entries with [f] applied, leaving
      [ctx] unmodified with the proviso that [f] does not modify the restricted
      set reference *)
  val map_entries : (entry -> 'a) -> t -> 'a list

  (** [get_ty entry] will extract the context type from an entry in the [ctx] *)
  val get_ty : entry -> d

  (** [get_restricted entry] returns the restricted set from [entry]*)
  val get_restricted : entry -> Res.t

  (** [get_id entry] returns the context variable id from an [entry]*)
  val get_id : entry -> v

  (** [get_blocks entry] gives the blocks from the [entry]*)
  val get_blocks : entry -> block list

  (** [get_schema entry] *)
  val get_schema : entry -> string

  (** [union ctx1 ctx2] returns a new [CtxVarCtx.t] which is the combination of
      [ctx1] and [ctx2]. Entries in [ctx2] replace those in [ctx1]. [ctx1] and
      [ctx2] are left unchanged *)
  val union : t -> t -> t
end

(** [ctxexpr_to_ctx ctxvars e] converts [e] into a context that can be used in
    type checking *)
val ctxexpr_to_ctx : CtxVarCtx.t -> ctx_expr -> (Term.var * Term.term) list

(** [replace_ctx_vars alist ctx] applies the substitution [alist] to the
    context variable in [ctx]*)
val replace_ctx_vars : (string * ctx_expr) list -> ctx_expr -> ctx_expr

(** [find_var_refs ctxvars tag ctx] gets all terms with [tag] from the context vars *)
val find_var_refs : CtxVarCtx.t -> Term.tag -> ctx_expr -> Term.term list

(** [get_explicit g] gives the list of vars and their types in context expression [g]
    such that the last item in the context is the first item in the list *)
val get_explicit : ctx_expr -> (Term.var * Term.term) list

(** [length g] returns the length of the context expression *)
val length : ctx_expr -> int

(** [context_prefix g1 g2] checks if [g1] is a prefix of [g2] *)
val context_prefix : ctx_expr -> ctx_expr -> bool

(** [remove_ctx_items expr ids] removes given [ids] from the context
    expression [expr]. Assumes ids exist in the explicit part of the
    context expression. *)
val remove_ctx_items : ctx_expr -> Term.id list -> ctx_expr

(** [block_prefix_sub sub_rel tys b1 b2] checks if [b1] is a prefix of [b2]
    where the extra items in [b2] cannot subordinate any types in [ids] *)
val block_prefix_sub
  :  Subordination.sub_rel
  -> Term.id list
  -> block_schema
  -> block_schema
  -> bool

(** [block_eq_sub sub_rel name b1 b2] checks if [b1] equal to [b2] after removing
    all types not subordinate to [name] *)
val block_eq_sub
  :  Subordination.sub_rel
  -> Term.id
  -> block_schema
  -> block_schema
  -> bool

(** [subordination_min sub_rel name g] returns a copy of the context expression [g]
    with all entries in the context that are not subordinate to [name] removed *)
val subordination_min : Subordination.sub_rel -> Term.id -> ctx_expr -> ctx_expr

(** [split_ctx g n] splits a context by the location of the variable [n].
    Returns the context to the left of n, the type of n, and the context
    to the right of n. Raises [Invalid_argument] if [n] is not in the context *)
val split_ctx : ctx_expr -> Term.id -> ctx_expr * Term.term * entry list
