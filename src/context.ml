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
      
let rec eq g1 g2 =
  match g1,g2 with
  | Nil, Nil -> true
  | Var v1, Var v2 -> var_eq v1 v2
  | Ctx(g1',(v1,t1)), Ctx(g2',(v2,t2)) ->
    v1=v2 && Term.eq t1 t2 && eq g1' g2'
  | _, _ -> false

let entry_eq (v1,t1) (v2,t2) =
  var_eq v1 v2
  &&
  Term.eq t1 t2 
              
let ctx_var s =  s
      
let ctx_var_eq = (fun x y -> x = y)

(* checks if there is a context variable in
   the given context expression.
   Returns true if there is, false otherwise. *)
let rec has_var =
  function
  | Nil -> false
  | Var _ -> true
  | Ctx(c,_) -> has_var c

(* given a context expression containing a context
   variable, returns the context variable. *)
let rec get_ctx_var =
  function
  | Var v -> v
  | Ctx(c,_) -> get_ctx_var c
  | _ -> assert false
  
let rec append_context ctx es =
  match es with
  | [] -> ctx
  | entry::es' ->
    append_context (Ctx(ctx,entry)) es'

let rec context_map f c =
  match c with
  | Nil | Var _ -> c
  | Ctx(c', (v,tm)) ->
    Ctx(context_map f c', (v, f tm))

let replace_ctx_expr_vars ?tag alist ctx =
  let rec aux c =
    match c with
    | Nil | Var _ -> c
    | Ctx(c', (v,tm)) ->
      let v' =
        try
          Term.term_to_var (List.assoc v.Term.name alist)
        with
        | Not_found -> v
      in 
      Ctx(aux c', (v',Term.replace_term_vars ?tag:tag alist tm))
  in
  aux ctx

(* returns the list of unique context variables appearing 
   in the given context expressions. *)
let get_used_ctxvars ctxs =
  let rec aux ctxs =
    match ctxs with
    | [] -> []
    | g::ctxs' ->
      if has_var g
      then
        (get_ctx_var g) :: (aux ctxs')
      else
        aux ctxs'
  in
  List.unique (aux ctxs)

let varcount = ref 1
let reset_varcount () = varcount := 1
let get_varcount () = !varcount
let set_varcount i = varcount := i 
    
let fresh =
    fun () ->
      let i = !varcount in
        incr varcount ;
        i

let fresh_name name used  =
  let rec aux () =
    let i = fresh () in
    let new_name = name ^ (string_of_int i) in
    if List.mem new_name used then aux ()
    else new_name
  in
  aux ()

let fresh_wrt name used =
  let id = fresh_name name used in
  (id, id::used)

    
(* context types *)
(* The blocks in the list are ordered from earliest in the context to latest. *)
type block = entry list
type ctx_typ = CtxTy of string * block list

let ctx_typ ?blocks:(blocks=[]) ~id () =
  CtxTy(id, blocks)

(* given a substitution for term variables, make the substitution
   within the given context type *)
let replace_ctx_typ_vars ?tag alist (CtxTy(id,blocks)) =
  CtxTy(id,List.map (fun lst -> List.map (fun (v,ty) -> (v, Term.replace_term_vars ?tag alist ty)) lst) blocks)
  
(* context schemas *)
type wctx = (Term.id * Type.ty) list 
type block_schema = B of wctx * entry list 
type ctx_schema = block_schema list
  
(* Given a context variable context will convert a given
   context expression into a context that can be used in
   type checking. *)                               
let rec ctxexpr_to_ctx ctxvars e =
  match e with
  | Nil -> []
  | Var id ->
     let CtxTy(_,blocks) = List.assoc id ctxvars in
     List.map (fun (v,ty) -> (v,ty)) (List.flatten blocks)
  | Ctx(e',(v,ty)) ->
     ((v,ty) :: (ctxexpr_to_ctx ctxvars e'))

(* given a context expression, apply the given substitution
   to the context variable, if there is one *)
let rec replace_ctx_vars alist ctx =
  let aux ctx =
    match ctx with
    | Nil -> Nil
    | Ctx(ctx', (v,tm)) -> Ctx(replace_ctx_vars alist ctx', (v,tm))
    | Var id ->
      (match List.assoc_opt id alist with
       | Some c -> c
       | None -> Var id)
  in
  aux ctx


let find_var_refs ctxvars tag ctx =
  let rec aux ctx =
    match ctx with
    | Nil -> []
    | Var v when List.mem_assoc v ctxvars ->
       let CtxTy(_,blocks) = List.assoc v ctxvars in
       if tag = Term.Nominal
       then
         (List.map (fun (x,_) -> Term.var_to_term x) (List.flatten blocks)) @
           (Term.find_var_refs tag (List.map snd (List.flatten blocks)))
       else
         Term.find_var_refs tag (List.map snd (List.flatten blocks))
    | Var _ ->  []
    | Ctx(ctx',(n,ty)) ->
      if tag = Term.Nominal
      then 
        (Term.var_to_term n) :: (Term.find_var_refs tag [ty] @ (aux ctx'))
      else
        Term.find_var_refs tag [ty] @ (aux ctx')
  in
  List.unique (aux ctx)


(* returns the explicit part of a context as a list.
   The last item added to the context will be the first
   item in the returned list. *)
let rec get_explicit = function
  | Nil -> []
  | Var _ -> []
  | Ctx(g,entry) -> entry :: (get_explicit g)

(* checks if context expression g1 is a prefix of the context expression g2 *)                               
let rec context_prefix g1 g2 =
  match g1, g2 with
  | Nil, _ -> true
  | Var(v1), Var(v2) -> var_eq v1 v2
  | Ctx(g1',(n1,t1)), Ctx(g2',(n2,t2)) -> 
     context_prefix g1 g2'
     || 
     (if n1 = n2 && Term.eq t1 t2
      then context_prefix g1' g2'
      else false)
  | _, Ctx(g2', _) -> context_prefix g1 g2'
  | _, _ -> false

let remove_ctx_items expr ids =
  let rec rem e =
    match e with 
    | Nil | Var _ ->  e 
    | Ctx(e',(n,t)) ->
       if List.mem n.name ids
       then
         rem e'
       else
         Ctx(rem e', (n,t))
  in
  rem expr

(* splits a context by the location of n.
   n is assumed to appear in the explicit part of g.
   returns the context to the left of n, the type of n, and the
   context to the right of n. *) 
let split_ctx g n =
  let rec find g g2 =
    match g with
    | Ctx(g', (n1,a1)) when n1.name = n ->
       (g', a1, (List.rev g2))
    | Ctx(g', e) ->
       find g' (e::g2)
    | _ -> assert false
  in
  find g []
