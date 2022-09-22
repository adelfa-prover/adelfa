(** [Context] is a representation of context expressions *)

(* context expressions *)

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

(** [ctx_schema] is a context schema [block_schema] *)
type ctx_schema = block_schema list

(** [ctxexpr_to_ctx ctxvars e] converts [e] into a context that can be used in
    type checking *)
val ctxexpr_to_ctx : (ctx_var * ctx_typ) list -> ctx_expr -> (Term.var * Term.term) list

(** [replace_ctx_vars alist ctx] applies the substitution [alist] to the
    context variable in [ctx]*)
val replace_ctx_vars : (string * ctx_expr) list -> ctx_expr -> ctx_expr

(** [find_var_refs ctxvars tag ctx] gets all terms with [tag] from the context vars *)
val find_var_refs : (ctx_var * ctx_typ) list -> Term.tag -> ctx_expr -> Term.term list

(** [get_explicit g] gives the list of vars and their types in context expression [g]
    such that the last item in the context is the first item in the list
*)
val get_explicit : ctx_expr -> (Term.var * Term.term) list

(** [context_prefix g1 g2] checks if [g1] is a prefix of [g2] *)
val context_prefix : ctx_expr -> ctx_expr -> bool

(** [remove_ctx_items expr ids] removes given [ids] from the context
    expression [expr]. Assumes ids exist in the explicit part of the
    context expression. *)
val remove_ctx_items : ctx_expr -> Term.id list -> ctx_expr

(** [split_ctx g n] splits a context by the location of the variable [n].
    Returns the context to the left of n, the type of n, and the context
    to the right of n. Raises [Invalid_argument] if [n] is not in the context *)
val split_ctx : ctx_expr -> Term.id -> ctx_expr * Term.term * entry list
