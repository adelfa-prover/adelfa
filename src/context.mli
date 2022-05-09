(** [Context] is a representation of context expressions *)

(* context expressions *)
type ctx_var = string
type entry = Term.var * Term.term

type ctx_expr =
  | Nil
  | Var of ctx_var
  | Ctx of ctx_expr * entry

val eq : ctx_expr -> ctx_expr -> bool
val entry_eq : entry -> entry -> bool
val ctx_var : string -> ctx_var
val ctx_var_eq : ctx_var -> ctx_var -> bool
val append_context : ctx_expr -> entry list -> ctx_expr
val context_map : (Term.term -> Term.term) -> ctx_expr -> ctx_expr

val replace_ctx_expr_vars
  :  ?tag:Term.tag
  -> (string * Term.term) list
  -> ctx_expr
  -> ctx_expr

val reset_varcount : unit -> unit
val get_varcount : unit -> int
val set_varcount : int -> unit
val fresh_wrt : string -> ctx_var list -> ctx_var * ctx_var list
val has_var : ctx_expr -> bool
val get_ctx_var : ctx_expr -> ctx_var
val get_used_ctxvars : ctx_expr list -> ctx_var list

(* context types *)
type block = entry list
type ctx_typ = CtxTy of string * block list

val ctx_typ : ?blocks:block list -> id:string -> unit -> ctx_typ

val replace_ctx_typ_vars
  :  ?tag:Term.tag
  -> (string * Term.term) list
  -> ctx_typ
  -> ctx_typ

(* context schemas *)
type wctx = (Term.id * Type.ty) list

(** [block_schema] represents a block schema in a context.

    A tuple where the first element represents the header variables with arity types
    and the second element represents the schematic variables *)
type block_schema = B of wctx * entry list

type ctx_schema = block_schema list

val ctxexpr_to_ctx : (ctx_var * ctx_typ) list -> ctx_expr -> (Term.var * Term.term) list
val replace_ctx_vars : (string * ctx_expr) list -> ctx_expr -> ctx_expr
val find_var_refs : (ctx_var * ctx_typ) list -> Term.tag -> ctx_expr -> Term.term list
val get_explicit : ctx_expr -> (Term.var * Term.term) list
val context_prefix : ctx_expr -> ctx_expr -> bool

(* removes given ids from the context expression. 
   Assumes ids exist in the explicit part of the context expression. *)
val remove_ctx_items : ctx_expr -> Term.id list -> ctx_expr
val split_ctx : ctx_expr -> Term.id -> ctx_expr * Term.term * entry list
