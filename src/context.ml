(*
 *
 * CONTEXT
 * Representation of context expressions
 * 
 *
 *)
include Extensions

(* context expressions *)
type ctx_var = string
type entry = Term.var * Term.term

type ctx_expr =
  | Nil
  | Var of ctx_var
  | Ctx of ctx_expr * entry

let var_eq v1 v2 = v1 = v2
let entry_eq (v1, t1) (v2, t2) = var_eq v1 v2 && Term.eq t1 t2

let rec eq g1 g2 =
  match g1, g2 with
  | Nil, Nil -> true
  | Var v1, Var v2 -> var_eq v1 v2
  | Ctx (g1', e1), Ctx (g2', e2) -> eq g1' g2' && entry_eq e1 e2
  | _, _ -> false
;;

let ctx_var s = s
let ctx_var_eq x y = x = y

let rec has_var = function
  | Nil -> false
  | Var _ -> true
  | Ctx (c, _) -> has_var c
;;

let rec get_ctx_var = function
  | Var v -> v
  | Ctx (c, _) -> get_ctx_var c
  | Nil -> raise (Invalid_argument "No ctx variable in context")
;;

let get_ctx_var_opt g =
  try Some (get_ctx_var g) with
  | Invalid_argument _ -> None
;;

let rec append_context ctx es =
  match es with
  | [] -> ctx
  | entry :: es' -> append_context (Ctx (ctx, entry)) es'
;;

let rec context_map f c =
  match c with
  | Nil | Var _ -> c
  | Ctx (c', (v, tm)) -> Ctx (context_map f c', (v, f tm))
;;

let replace_ctx_expr_vars ?tag alist ctx =
  let rec aux c =
    match c with
    | Nil | Var _ -> c
    | Ctx (c', (v, tm)) ->
      let v' =
        try Term.term_to_var (List.assoc v.Term.name alist) with
        | Not_found -> v
      in
      Ctx (aux c', (v', Term.replace_term_vars ?tag alist tm))
  in
  aux ctx
;;

let get_used_ctxvars ctxs =
  let rec aux ctxs =
    match ctxs with
    | [] -> []
    | g :: ctxs' -> if has_var g then get_ctx_var g :: aux ctxs' else aux ctxs'
  in
  List.unique (aux ctxs)
;;

let varcount = ref 1
let reset_varcount () = varcount := 1
let get_varcount () = !varcount
let set_varcount i = varcount := i
let remove_trailing_numbers s = Str.global_replace (Str.regexp "[0-9]*$") "" s

let fresh_name name used =
  let basename = remove_trailing_numbers name in
  let rec aux i =
    let name = basename ^ string_of_int i in
    if List.mem name used then aux (i + 1) else name
  in
  (* Try to avoid any renaming *)
  if List.mem name used then aux 1 else name
;;

let fresh_wrt name used =
  let id = fresh_name name used in
  id, id :: used
;;

(* context types *)
type block = entry list
type ctx_typ = CtxTy of string * block list

let ctx_typ ?(blocks = []) ~id () = CtxTy (id, blocks)

let replace_ctx_typ_vars ?tag alist (CtxTy (id, blocks)) =
  CtxTy
    ( id
    , List.map
        (fun lst -> List.map (fun (v, ty) -> v, Term.replace_term_vars ?tag alist ty) lst)
        blocks )
;;

(* context schemas *)

type wctx = (Term.id * Type.ty) list
type block_schema = B of wctx * entry list
type ctx_schema = block_schema list

let rec ctxexpr_to_ctx ctxvars e =
  match e with
  | Nil -> []
  | Var id ->
    let (CtxTy (_, blocks)) = List.assoc id ctxvars in
    List.map (fun (v, ty) -> v, ty) (List.flatten blocks)
  | Ctx (e', (v, ty)) -> (v, ty) :: ctxexpr_to_ctx ctxvars e'
;;

let replace_ctx_vars alist ctx =
  let rec aux ctx =
    match ctx with
    | Nil -> Nil
    | Ctx (ctx', (v, tm)) -> Ctx (aux ctx', (v, tm))
    | Var id ->
      (match List.assoc_opt id alist with
       | Some c -> c
       | None -> Var id)
  in
  aux ctx
;;

let find_var_refs ctxvars tag ctx =
  let rec aux ctx =
    match ctx with
    | Nil -> []
    | Var v when List.mem_assoc v ctxvars ->
      let (CtxTy (_, blocks)) = List.assoc v ctxvars in
      if tag = Term.Nominal
      then
        List.map (fun (x, _) -> Term.var_to_term x) (List.flatten blocks)
        @ Term.find_var_refs tag (List.map snd (List.flatten blocks))
      else Term.find_var_refs tag (List.map snd (List.flatten blocks))
    | Var _ -> []
    | Ctx (ctx', (n, ty)) ->
      if tag = Term.Nominal
      then Term.var_to_term n :: (Term.find_var_refs tag [ ty ] @ aux ctx')
      else Term.find_var_refs tag [ ty ] @ aux ctx'
  in
  List.unique (aux ctx)
;;

let rec get_explicit = function
  | Nil -> []
  | Var _ -> []
  | Ctx (g, entry) -> entry :: get_explicit g
;;

let length ctx =
  let rec aux acc ctx =
    match ctx with
    | Nil | Var _ -> acc + 1
    | Ctx (ctx', _) -> aux (acc + 1) ctx'
  in
  aux 0 ctx
;;

(* checks if context expression g1 is a prefix of the context expression g2 *)
let rec context_prefix g1 g2 =
  match g1, g2 with
  | Nil, _ -> true
  | Var v1, Var v2 -> var_eq v1 v2
  | Ctx (g1', (n1, t1)), Ctx (g2', (n2, t2)) ->
    context_prefix g1 g2'
    || if n1 = n2 && Term.eq t1 t2 then context_prefix g1' g2' else false
  | _, Ctx (g2', _) -> context_prefix g1 g2'
  | _, _ -> false
;;

let remove_ctx_items expr ids =
  let rec rem e =
    match e with
    | Nil | Var _ -> e
    | Ctx (e', (n, t)) -> if List.mem n.name ids then rem e' else Ctx (rem e', (n, t))
  in
  rem expr
;;

(* splits a context by the location of n.
   n is assumed to appear in the explicit part of g.
   returns the context to the left of n, the type of n, and the
   context to the right of n. *)
let split_ctx g n =
  let rec find g g2 =
    match g with
    | Ctx (g', (n1, a1)) when n1.name = n -> g', a1, List.rev g2
    | Ctx (g', e) -> find g' (e :: g2)
    | _ -> raise (Invalid_argument "n must be in the explicit context")
  in
  find g []
;;
