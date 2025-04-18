(*
 * TERM
 * Representation of the terms of the logic. 
 * 
 * These terms represent LF expressions and can be viewed as
 * simply-typed terms in a weakly typed setting or as
 * dependently-typed terms in an LF setting.
 *)

open Type
open Extensions

type tag =
  | Eigen
  | Constant
  | Logic
  | Nominal

type id = string

(* Note about timestamps: Constants from sig are all at the outtermost level, ts = 0 Then
   are all the eigenvariables, ts = 1 Then there are the bound variables, ts = 2 Finally,
   nominals are also at the same as bound vars, ts = 2*)
type var =
  { name : id
  ; tag : tag
  ; ts : int
  ; ty : ty
  }

type t = var
type tyctx = (id * ty) list

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

(* type contexts for abstractions and pis identify LF types for bound variables. *)
and lftyctx = (var * term) list
and env = envitem list

and envitem =
  | Dum of int
  | Binding of term * int

and ptr = in_ptr ref

and in_ptr =
  | V of var
  | T of term

(* Utilities for constructing and deconstructing terms *)

(* Assumes that the arity types of the variables
 * match the erased form of the LF types associated
 * with them in the given context. *)
let lftyctx_to_tyctx lftyctx = List.map (fun (v, _) -> v.name, v.ty) lftyctx

let rec observe = function
  | Ptr { contents = T d } -> observe d
  | Ptr { contents = V v } -> Var v
  | t -> t
;;

let rename_vars alist (t : term) =
  let rec aux t =
    match t with
    | Var v ->
      (match List.assoc_opt v.name alist with
       | Some v' -> Var { v with name = v' }
       | None -> Var v)
    | DB i -> DB i
    | Lam (tyctx, t') -> Lam (tyctx, aux t')
    | App (t, ts) -> App (aux t, List.map aux ts)
    | Susp (t, i, j, e) -> Susp (aux t, i, j, e)
    | Ptr p ->
      (match p with
       | { contents = V v } ->
         Ptr
           { contents =
               V { v with name = Option.default v.name (List.assoc_opt v.name alist) }
           }
       | { contents = T t } -> Ptr { contents = T (aux t) })
    | Pi (bndrs, t') -> Pi (bndrs, aux t')
    | Type -> Type
  in
  aux t
;;

let db n = DB n
let get_ctx_tys tyctx = List.map snd tyctx
let get_lfctx_tys lftyctx = List.map snd lftyctx

let rec lambda idtys t =
  if idtys = []
  then t
  else (
    match t with
    | Lam (idtys', t') -> lambda (idtys @ idtys') t'
    | _ -> Lam (idtys, t))
;;

let app a b =
  if b = []
  then a
  else (
    match observe a with
    | App (a, c) -> App (a, c @ b)
    | _ -> App (a, b))
;;

let susp t ol nl e = Susp (t, ol, nl, e)

let rec pi lfidtys t =
  if lfidtys = []
  then t
  else (
    match t with
    | Pi (lfidtys', t') -> pi (lfidtys @ lfidtys') t'
    | _ -> Pi (lfidtys, t))
;;

(* Normalization and Equality *)

(* Raise the substitution *)
let rec add_dummies env n m =
  match n with
  | 0 -> env
  | _ ->
    let n' = n - 1 in
    Dum (m + n') :: add_dummies env n' m
;;

(** Make an environment appropriate to [n] lambda abstractions applied to
    the arguments in [args]. Return the environment together with any
    remaining lambda abstractions and arguments. (There can not be both
    abstractions and arguments left over). *)
let make_env n args =
  let rec aux n args e =
    if n = 0 || args = []
    then e, n, args
    else aux (n - 1) (List.tl args) (Binding (List.hd args, 0) :: e)
  in
  aux n args []
;;

(** Head normalization function.*)
let rec hnorm term =
  match observe term with
  | Var _ | DB _ | Type -> term
  | Lam (idtys, t) -> lambda idtys (hnorm t)
  | Pi (idtys, t) -> pi idtys (hnorm t)
  | App (t, []) -> hnorm t
  | App (t, args) ->
    let t = hnorm t in
    (match observe t with
     | Lam (idtys, t) ->
       let n = List.length idtys in
       let e, n', args' = make_env n args in
       let ol = List.length e in
       if n' > 0
       then hnorm (susp (lambda (List.drop (n - n') idtys) t) ol 0 e)
       else hnorm (app (susp t ol 0 e) args')
     (* Do we actually need to treat this differently from an *)
     (* abstraction? besides considering the LF types. *)
     | Pi (lfidtys, t) ->
       (* should be ok to assume that number of args is less than pi-bound variables *)
       let n = List.length args in
       let alist = List.map2 (fun (v, _) a -> v.name, a) (List.take n lfidtys) args in
       pi
         (List.map (fun (v, ty) -> v, replace_term_vars alist ty) (List.drop n lfidtys))
         (hnorm (replace_term_vars alist t))
     (* | Pi(lfidtys,t) -> *)
     (*    let n = List.length lfidtys in *)
     (*    let e, n', args' = make_env n args in *)
     (*    let ol = List.length e in *)
     (*    if n' > 0 *)
     (*    then hnorm (susp (pi (List.drop (n-n') lfidtys) t) ol 0 e)  *)
     (*    else hnorm (app (susp t ol 0 e) args')  *)
     | _ -> app t args)
  | Susp (t, ol, nl, e) ->
    let t = hnorm t in
    (match observe t with
     | Var _ | Type -> t
     | DB i ->
       if i > ol
       then (* The index points to something outside the suspension *)
         db (i - ol + nl)
       else (
         (* The index has to be substituted for [e]'s [i]th element *)
         match List.nth e (i - 1) with
         | Dum l -> db (nl - l)
         | Binding (t, l) -> hnorm (susp t 0 (nl - l) []))
     | Lam (idtys, t) ->
       let n = List.length idtys in
       lambda idtys (hnorm (susp t (ol + n) (nl + n) (add_dummies e n nl)))
     | Pi (lfidtys, t) ->
       let n = List.length lfidtys in
       (* need to apply within the types of bound variables as well *)
       let lfidtys' =
         List.mapi
           (fun i (v, tm) -> v, hnorm (susp tm (ol + i) (nl + i) (add_dummies e i nl)))
           lfidtys
       in
       pi lfidtys' (hnorm (susp t (ol + n) (nl + n) (add_dummies e n nl)))
     | App (t, args) ->
       let wrap x = susp x ol nl e in
       hnorm (app (wrap t) (List.map wrap args))
     | Susp _ -> assert false
     | Ptr _ -> assert false)
  | Ptr _ -> assert false

(* This replacement assumes that binding issues like name capture are *)
(* handled by the caller. *)
and replace_term_vars ?tag alist t =
  let rec aux t =
    match observe (hnorm t) with
    | Var v when List.mem_assoc v.name alist && (tag = None || tag = Some v.tag) ->
      List.assoc v.name alist
    | Var _ | DB _ | Type -> t
    | Lam (i, t) -> lambda i (aux t)
    | Pi (is, t) -> pi (List.map (fun (v, ty) -> v, aux ty) is) (aux t)
    | App (t, ts) -> app (aux t) (List.map aux ts)
    | Susp _ -> assert false
    | Ptr _ -> assert false
  in
  aux t
;;

let rec norm t =
  match observe (hnorm t) with
  | (Var _ | DB _) as t -> t
  | App (f, ts) -> app (norm f) (List.map norm ts)
  | Lam (cx, t) -> lambda cx (norm t)
  | Pi (lfcx, t) -> pi (List.map (fun (v, ty) -> v, norm ty) lfcx) (norm t)
  | _ -> assert false
;;

let is_uninstantiated (x, vtm) =
  match observe (hnorm vtm) with
  | Var { name = n; tag = Eigen; _ } when n = x -> true
  | _ -> false
;;

(* Given a term t, returns the eta-normal form of t. *)
let rec eta_normalize t =
  match norm t with
  | Lam (idtys, App (h, ts)) ->
    let n = min (List.length idtys) (List.length ts) in
    let ts' = List.map eta_normalize ts in
    if List.fold_left2
         (fun acc bndr arg ->
           match norm arg with
           | Var v -> fst bndr = v.name && acc
           | DB i ->
             (try
                let bndr' = List.nth (List.rev idtys) i in
                bndr' = bndr && acc
              with
              | _ -> false)
           | _ -> false)
         true
         (List.take n idtys)
         (List.take_last n ts')
    then app h (List.drop_last n ts')
    else lambda idtys (app h ts')
  | App (h, ts) -> app h (List.map eta_normalize ts)
  | _ as t -> t
;;

let rec alpha_eq t1 t2 mappings =
  let try_map_vars v1 v2 mappings =
    if v1.ts <> v2.ts
    then None
    else if v1.ts = 0 && v2.ts = 0
    then if v1.name = v2.name then Some mappings else None
    else (
      match List.assoc_opt v1.name mappings with
      | Some v1' -> if v1' = v2.name then Some mappings else None
      | None ->
        if List.exists (fun (_, dst) -> v2.name = dst) mappings
        then None
        else Some ((v1.name, v2.name) :: mappings))
  in
  match norm t1, norm t2 with
  | DB i1, DB i2 -> if i1 = i2 then Some mappings else None
  | Var v1, Var v2 -> try_map_vars v1 v2 mappings
  | App (h1, l1), App (h2, l2) ->
    if List.length l1 <> List.length l2
    then None
    else
      List.fold_left2
        (fun acc t1 t2 ->
          match acc with
          | Some mappings -> alpha_eq t1 t2 mappings
          | None -> None)
        (alpha_eq h1 h2 mappings)
        l1
        l2
  | Lam (idtys1, t1), Lam (idtys2, t2) ->
    if get_ctx_tys idtys1 <> get_ctx_tys idtys2 then None else alpha_eq t1 t2 mappings
  | Pi (idtys1, t1), Pi (idtys2, t2) ->
    if get_ctx_tys idtys1 <> get_ctx_tys idtys2 then None else alpha_eq t1 t2 mappings
  | Type, Type -> Some mappings
  | _ -> Some mappings
;;

let rec eq t1 t2 =
  match norm t1, norm t2 with
  | DB i1, DB i2 -> i1 = i2
  | Var v1, Var v2 -> v1 = v2
  | App (h1, l1), App (h2, l2) ->
    List.length l1 = List.length l2 && List.for_all2 eq (h1 :: l1) (h2 :: l2)
  | Lam (idtys1, t1), Lam (idtys2, t2) ->
    get_ctx_tys idtys1 = get_ctx_tys idtys2 && eq t1 t2
  | Pi (idtys1, t1), Pi (idtys2, t2) ->
    get_lfctx_tys idtys1 = get_lfctx_tys idtys2 && eq t1 t2
  | Type, Type -> true
  | _ -> false
;;

let rec get_ty_head tm =
  match observe (hnorm tm) with
  | Pi (_, h) -> get_ty_head h
  | App (t, _) -> get_ty_head t
  | Var v -> v.name
  | _ -> bugf "Cannot get type of head"
;;

let rec is_kind tm =
  match observe (hnorm tm) with
  | Pi (_, h) -> is_kind h
  | Type -> true
  | _ -> false
;;

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. *)

(* bind_state is a list of (var, old_value, new_value) *)
type bind_state = (ptr * in_ptr * term) list

let bind_state : bind_state ref = State.rref []
let bind_len = State.rref 0

let rec deref = function
  | Ptr { contents = T t } -> deref t
  | t -> t
;;

let getref = function
  | Ptr t -> t
  | _ -> assert false
;;

let bind v t =
  let dv = getref (deref v) in
  let dt = deref t in
  assert (
    match dt with
    | Ptr r -> dv != r
    | _ -> true);
  bind_state := (dv, !dv, dt) :: !bind_state;
  incr bind_len;
  dv := T dt
;;

let get_bind_state () = !bind_state

let clear_bind_state () =
  List.iter (fun (v, ov, _) -> v := ov) !bind_state;
  bind_state := [];
  bind_len := 0
;;

let set_bind_state state =
  clear_bind_state ();
  List.iter (fun (v, _, nv) -> bind (Ptr v) nv) (List.rev state)
;;

let () =
  State.add_hook ~time:BeforeReload (fun () ->
    List.iter (fun (v, ov, _) -> v := ov) !bind_state)
;;

let () = State.add_hook ~time:AfterReload (fun () -> set_bind_state !bind_state)

(* Scoped bind state is more efficient than regular bind state, but it must always be used
   in a lexically scoped fashion. The unwind_state wraps a function with a scoped get and
   set. *)

type scoped_bind_state = int

let get_scoped_bind_state () = !bind_len

let set_scoped_bind_state state =
  while !bind_len > state do
    match !bind_state with
    | (v, ov, _) :: rest ->
      v := ov;
      bind_state := rest;
      decr bind_len
    | [] -> assert false
  done
;;

let unwind_state f x =
  let state = get_scoped_bind_state () in
  let result = f x in
  set_scoped_bind_state state;
  result
;;

(* Recursively raise dB indices and abstract over variables
 * selected by [test]. Indices unprotected by abstractions
 * are incremented. *)
let abstract test =
  let rec aux n t =
    match t with
    | DB i -> DB (if i < n then i else i + 1)
    | App (h, ts) -> app (aux n h) (List.map (aux n) ts)
    | Lam (idtys, s) -> lambda idtys (aux (n + List.length idtys) s)
    | Pi (lfidtys, s) -> pi lfidtys (aux (n + List.length lfidtys) s)
    | Ptr { contents = T t } -> Ptr (ref (T (aux n t)))
    | Ptr { contents = V v } -> if test t v.name then DB n else t
    | Type | Var _ -> assert false
    | Susp _ -> assert false
  in
  aux
;;

(** Abstract (object) [t] over constant or variable [v]. *)
let abstract id ty t = lambda [ id, ty ] (abstract (fun _ id' -> id' = id) 1 t)

(** Utilities.
    * Easy creation of constants and variables, with sharing. *)

let nominal_var name ty = Ptr (ref (V { name; tag = Nominal; ts = max_int; ty }))

let var tag name ts ty =
  if tag = Nominal then nominal_var name ty else Ptr (ref (V { name; tag; ts; ty }))
;;

let const ?(ts = 0) s ty = Ptr (ref (V { name = s; ts; tag = Constant; ty }))
let logic ?(ts = 1) s ty = Ptr (ref (V { name = s; ts; tag = Logic; ty }))

let get_id t =
  match observe (hnorm t) with
  | Var v -> v.name
  | _ -> bugf "Cannot get id of term"
;;

let compare t1 t2 = String.compare t1.name t2.name

let get_tag t =
  match observe t with
  | Var v -> v.tag
  | _ -> bugf "Cannot get tag of term"
;;

let is_var tag t =
  match observe (hnorm t) with
  | Var v -> v.tag = tag
  | _ -> false
;;

let rec get_hd_id t =
  match observe (hnorm t) with
  | App (h, _) -> get_hd_id h
  | Lam (_, btm) -> get_hd_id btm
  | Var v -> v.name
  | _ -> bugf "Cannot get id of head"
;;

let get_var_ty t =
  match observe (hnorm t) with
  | Var v -> v.ty
  | Lam _ ->
    (match eta_normalize t with
     | Var v -> v.ty
     | _ -> exit 1)
  | _ -> assert false
;;

module Notations = struct
  let ( // ) = lambda
  let ( ^^ ) = app
end

let prefix = function
  | Constant -> "c"
  | Logic -> "?"
  | Eigen -> "X"
  | Nominal -> "n"
;;

let varcount = State.rref 1
let reset_varcount () = varcount := 1
let get_varcount () = !varcount
let set_varcount i = varcount := i

let fresh' () =
  let i = !varcount in
  incr varcount;
  i
;;

let fresh ?(tag = Logic) ?(ts = 1) ty =
  let i = fresh' () in
  let name = prefix tag ^ string_of_int i in
  var tag name ts ty
;;

(* given a variable term, eta expand into equivallent term in eta long form. *)
let rec eta_expand t =
  match observe (hnorm t) with
  | Var v ->
    (match v.ty with
     | Type.Ty ([], _) -> t
     | Type.Ty (tyargs, _) ->
       let bvars = List.map (fresh ~tag:Constant ~ts:2) tyargs in
       List.fold_right2
         (fun name ty btm -> abstract (get_hd_id name) ty btm)
         bvars
         tyargs
         (app t (List.map eta_expand bvars)))
  | Lam (tyctx, body) -> lambda tyctx (eta_expand body)
  | App (h, tms) -> app (eta_expand h) (List.map eta_expand tms)
  | Pi (lctx, t) -> Pi (lctx, eta_expand t)
  | DB _ -> t
  | Type -> bugf "Eta expanded invalid type"
  | Susp _ -> bugf "Eta expanded invalid susp"
  | Ptr _ -> bugf "Eta expanded invalid ptr"
;;

let remove_trailing_numbers s = Str.global_replace (Str.regexp "[0-9]*$") "" s

let fresh_name name used =
  let basename = remove_trailing_numbers name in
  let rec aux i =
    let name = basename ^ string_of_int i in
    if List.mem_assoc name used then aux (i + 1) else name
  in
  (* Try to avoid any renaming *)
  if List.mem_assoc name used then aux 1 else name
;;

let fresh_wrt ~ts tag name ty used =
  let name = fresh_name name used in
  let v = var tag name ts ty in
  v, (name, v) :: used
;;

let term_to_var t =
  match observe (hnorm t) with
  | Var v -> v
  | _ -> assert false
;;

let term_to_name t = (term_to_var t).name
let term_to_pair t = term_to_name t, t
let var_to_term v = var v.tag v.name v.ts v.ty

(* Select all variable references which satisfy f *)
let select_var_refs f ts =
  let rec fv acc t =
    let t = hnorm t in
    match observe t with
    | Var v -> if f v then t :: acc else acc
    | App (h, ts) -> List.fold_left fv (fv acc h) ts
    | Lam (_, t') -> fv acc t'
    | Pi (lfidtys, t') -> List.fold_left fv (fv acc t') (List.map snd lfidtys)
    | DB _ | Type -> acc
    | Susp _ -> assert false
    | Ptr _ -> assert false
  in
  List.fold_left fv [] ts
;;

let find_var_refs tag ts = List.unique (select_var_refs (fun v -> v.tag = tag) ts)
let find_vars tag ts = List.map term_to_var (find_var_refs tag ts)

let get_used ts =
  select_var_refs (fun _ -> true) ts |> List.rev |> List.unique |> List.map term_to_pair
;;

(* Typing *)

let rec tc (tyctx : tyctx) t =
  match observe (hnorm t) with
  | DB i -> snd (List.nth tyctx (i - 1))
  | Var v -> v.ty
  | App (h, args) ->
    let arg_tys = List.map (tc tyctx) args in
    (match tc tyctx h with
     | Ty (tys, bty) ->
       let n = List.length arg_tys in
       assert (List.take n tys = arg_tys);
       Ty (List.drop n tys, bty))
  | Lam (idtys, t) -> tyarrow (get_ctx_tys idtys) (tc (List.rev_append idtys tyctx) t)
  | _ -> assert false
;;

(* erase a term into the correponding arity type *)

let rec erase t =
  match observe (hnorm t) with
  | Pi (tys, t) ->
    (match erase t with
     | Ty (tys', bty) ->
       let tys = List.map (fun x -> erase (snd x)) tys in
       Ty (tys @ tys', bty))
  | Var v when v.tag = Constant -> oty
  | App _ -> oty
  | Type -> oty
  | _ -> assert false
;;

let convert_to_nominals bndrs used =
  let rec aux bndrs used =
    match bndrs with
    | [] -> []
    | (h, _) :: tl ->
      let v, newused = fresh_wrt ~ts:3 Nominal "n" h.ty used in
      v :: aux tl newused
  in
  aux bndrs used
;;

module Print = struct
  let pr_var ppf v = Format.fprintf ppf "%s" v.name
  let pr_str ppf s = Format.fprintf ppf "%s" s

  let db_to_string cx0 i0 =
    let rec spin cx i =
      match cx, i with
      | [], _ -> "x" ^ string_of_int (i0 - List.length cx0 + 1)
      | name :: _, 1 -> name
      | _ :: cx, _ -> spin cx (i - 1)
    in
    spin cx0 i0
  ;;

  let rec pr_term_literal ppf t =
    match t with
    | Var v -> Format.fprintf ppf "@[<2>Var(@,%a@,)@]" pr_var_literal v
    | DB i -> Format.fprintf ppf "@[<2>DB(@,%a@,)@]" pr_str (string_of_int i)
    | Lam (idtys, tm) ->
      Format.fprintf ppf "@[<2>Lam(@,[%a],@,%a)@]" pr_idlst idtys pr_term_literal tm
    | App (h, tms) ->
      Format.fprintf ppf "@[<2>App(@,%a,@,[%a]@,)@]" pr_term_literal h pr_tmlst tms
    | Pi (lfidtys, tm) ->
      Format.fprintf ppf "@[<2>Pi(@,[%a],@,%a)@]" pr_lfidlst lfidtys pr_term_literal tm
    | Type -> pr_str ppf "Type"
    | Ptr p -> Format.fprintf ppf "@[<2>Ptr(@,%a@,)@]" pr_ptr_literal p
    | Susp _ -> pr_term_literal ppf (hnorm t)

  and pr_var_literal ppf v =
    let string_of_tag = function
      | Eigen -> "Eigen"
      | Constant -> "Constant"
      | Logic -> "Logic"
      | Nominal -> "Nominal"
    in
    Format.fprintf
      ppf
      "name=%a,@,tag=%a,@,ts=%a,@,ty=%a"
      pr_str
      v.name
      pr_str
      (string_of_tag v.tag)
      pr_str
      (string_of_int v.ts)
      Type.Print.pr_ty_literal
      v.ty

  and pr_ptr_literal ppf p =
    match !p with
    | V v -> Format.fprintf ppf "V(@,Var(%a))" pr_var_literal v
    | T t -> Format.fprintf ppf "T(@,%a)" pr_term_literal t

  and pr_lfidlst ppf lfidtys =
    match lfidtys with
    | [] -> Format.fprintf ppf "@,"
    | [ (v, ty) ] -> Format.fprintf ppf "@,(%a,%a)@," pr_str v.name pr_term_literal ty
    | (v, ty) :: lfidtys' ->
      Format.fprintf
        ppf
        "@,(%a,%a)@,,%a"
        pr_str
        v.name
        pr_term_literal
        ty
        pr_lfidlst
        lfidtys'

  and pr_idlst ppf idtys =
    match idtys with
    | [] -> Format.fprintf ppf "@,"
    | [ (id, ty) ] -> Format.fprintf ppf "%a:%a" pr_str id Type.Print.pr_ty_literal ty
    | (id, ty) :: idtys' ->
      Format.fprintf
        ppf
        "%a:%a;@, %a"
        pr_str
        id
        Type.Print.pr_ty_literal
        ty
        pr_idlst
        idtys'

  and pr_tmlst ppf tms =
    match tms with
    | [] -> Format.fprintf ppf "@,"
    | [ tm ] -> pr_term_literal ppf tm
    | tm :: tms' -> Format.fprintf ppf "%a;@, %a" pr_term_literal tm pr_tmlst tms'
  ;;

  let rec pr_term cx ppf t =
    match observe (hnorm t) with
    | Var v -> pr_var ppf v
    | DB i -> pr_db cx ppf i
    | Lam (idtys, tm) -> pr_lam cx ppf idtys tm
    | App (h, tms) -> pr_app cx ppf h tms
    | Pi (idtys, tm) -> pr_pi cx ppf idtys tm
    | Type -> pr_str ppf "type"
    | _ -> assert false

  and pr_term' cx ppf t =
    match observe (hnorm t) with
    | Var v -> pr_var ppf v
    | DB i -> pr_db cx ppf i
    | Lam (idtys, tm) -> Format.fprintf ppf "(%a)" (fun ppf -> pr_lam cx ppf idtys) tm
    | App _ -> Format.fprintf ppf "(%a)" (pr_term cx) t
    | Pi (idtys, tm) -> pr_pi cx ppf idtys tm
    | Type -> pr_str ppf "type"
    | _ -> assert false

  and pr_db cx ppf i = pr_str ppf (db_to_string cx i)

  and pr_app cx ppf h tms =
    let rec pr_args ppf tms =
      match tms with
      | [] -> ()
      | t :: tms' -> Format.fprintf ppf "@ %a%a" (pr_term' cx) t pr_args tms'
    in
    Format.fprintf ppf "@[<hov 2>%a%a@]" (pr_term cx) h pr_args tms

  and pr_lam cx ppf idtys tm =
    let rec pr_bndr cx ppf idtys =
      match idtys with
      | [] -> pr_term cx ppf tm
      | (n, _) :: idtys' ->
        Format.fprintf ppf "@[<2>[@,%a@,]%a@]" pr_str n (pr_bndr (n :: cx)) idtys'
    in
    pr_bndr cx ppf idtys

  and pr_pi cx ppf idtys tm =
    let rec pr_bndr cx ppf idtys =
      match idtys with
      | [] -> pr_term cx ppf tm
      | (v, k) :: idtys' ->
        Format.fprintf
          ppf
          "@[<2>{@,%a@,:@,%a@,}%a@]"
          pr_var
          v
          (pr_term cx)
          k
          (pr_bndr (v.name :: cx))
          idtys'
    in
    pr_bndr cx ppf idtys
  ;;

  let string_of_term_literal tm =
    pr_term_literal Format.str_formatter tm;
    Format.flush_str_formatter ()
  ;;

  let string_of_term tm =
    pr_term [] Format.str_formatter tm;
    Format.flush_str_formatter ()
  ;;

  let rec pr_varlst ppf lst =
    match lst with
    | [] -> ()
    | [ (id, t) ] ->
      Format.fprintf ppf "%a@,:@,%a" pr_str id Type.Print.pr_ty (get_var_ty t)
    (* pr_str ppf id *)
    | (id, t) :: vs ->
      Format.fprintf
        ppf
        "%a@,:@,%a,@ %a"
        pr_str
        id
        Type.Print.pr_ty
        (get_var_ty t)
        pr_varlst
        vs
  ;;
end
