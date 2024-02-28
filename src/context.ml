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

let rec context_filter f c =
  match c with
  | Nil | Var _ -> c
  | Ctx (c', (_, e)) when f e -> context_filter f c'
  | Ctx (c', (v, tm)) -> Ctx (context_filter f c', (v, tm))
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

let list_fresh_wrt names used =
  let used = ref used in
  let cvars_alist =
    List.fold_left
      (fun acc (v, t) ->
        let v', used' = fresh_wrt v !used in
        used := used';
        (v, v', t) :: acc)
      []
      names
  in
  cvars_alist, !used
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

module CtxVarCtx = struct
  module H = Extensions.Hashtbl
  module Res = VarSet

  type v = ctx_var
  type ctx_ty = ctx_typ
  type d = Res.t ref * ctx_ty
  type entry = v * d
  type t = (v, d) H.t

  let empty () = H.create 19
  let is_empty ctx = H.length ctx = 0
  let add_var ctx v ?(res = Res.empty) blocks = H.replace ctx v (ref res, blocks)

  let add_var ctx v ?(res = []) blocks =
    let set = Res.add_vars Res.empty res in
    add_var ctx v ~res:set blocks
  ;;

  let mem t v = H.mem t v
  let add_vars ctx vs = H.replace_seq ctx (List.to_seq vs)
  let find_var_opt t v = H.find_opt t v
  let find t v = H.find t v
  let to_list ctx = H.to_seq ctx |> List.of_seq

  let of_list entries =
    let ctx = empty () in
    List.iter (fun (k, (r, b)) -> H.replace ctx k (r, b)) entries;
    ctx
  ;;

  let of_list_list entries =
    let ctx = empty () in
    List.iter (fun (k, (r, b)) -> add_var ctx k ~res:r b) entries;
    ctx
  ;;

  let get_vars ctx = to_list ctx |> List.map fst

  let restrict_in t var noms =
    match find_var_opt t var with
    | Some (r, _) -> r := Res.add_vars !r noms
    | None -> ()
  ;;

  let remove_var ctx v = H.remove ctx v

  let copy ctx =
    let copy_entry (k, (res, bl)) = k, (ref (Res.copy !res), bl) in
    let new_ctx = empty () in
    let new_entries = H.to_seq ctx |> Seq.map copy_entry in
    H.replace_seq new_ctx new_entries;
    new_ctx
  ;;

  let get_var_ty ctx var =
    let* _, ty = find_var_opt ctx var in
    return ty
  ;;

  let get_var_blocks ctx var =
    match get_var_ty ctx var with
    | None -> []
    | Some (CtxTy (_, b)) -> b
  ;;

  let get_var_schema ctx var =
    let* (CtxTy (s, _)) = get_var_ty ctx var in
    return s
  ;;

  let get_var_tys ctx = to_list ctx |> List.map (fun (v, (_, b)) -> v, b)

  let get_var_restricted ctx var =
    let* res, _ = find_var_opt ctx var in
    return !res
  ;;

  let remove_all f ctx =
    let f' k v = if f k v then None else Some v in
    H.filter_map_inplace f' ctx
  ;;

  let map_inplace f ctx =
    let f' k v = Some (f k v) in
    H.filter_map_inplace f' ctx
  ;;

  let map_entries f ctx = to_list ctx |> List.map f

  let get_ty entry =
    match entry with
    | _, e -> e
  ;;

  let get_restricted entry =
    match entry with
    | _, (s, _) -> !s
  ;;

  let get_id entry =
    match entry with
    | id, _ -> id
  ;;

  let get_blocks entry =
    match entry with
    | _, (_, CtxTy (_, b)) -> b
  ;;

  let get_schema entry =
    match entry with
    | _, (_, CtxTy (s, _)) -> s
  ;;

  let union ctx1 ctx2 =
    let ctx1' = copy ctx1 in
    let ctx2_entries = copy ctx2 |> H.to_seq in
    let () = H.replace_seq ctx1' ctx2_entries in
    ctx1'
  ;;
end

let rec ctxexpr_to_ctx ctxvars e =
  match e with
  | Nil -> []
  | Var id ->
    let blocks = CtxVarCtx.get_var_blocks ctxvars id in
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
    | Var v when CtxVarCtx.mem ctxvars v ->
      let blocks = CtxVarCtx.get_var_blocks ctxvars v in
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

let subordination_min graph t expr =
  context_filter
    (fun n -> not (Subordination.subordinates graph (Term.get_ty_head n) t))
    expr
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
