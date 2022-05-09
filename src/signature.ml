(*
 *
 * SIGNATURE
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

let ty_dec n k i f os = { ty_name = n; kind = k; ty_implicit = i; ty_fix = f; objs = os }
let obj_dec n t i f = { obj_name = n; typ = t; obj_implicit = i; obj_fix = f }
let add_obj_to_ty td id = td.objs <- id :: td.objs

type signature = (id * type_decl) list * (id * obj_decl) list

let empty = [], []
let get_type_decls (tds, _) = List.map snd tds
let get_obj_decls (_, ods) = List.map snd ods
let add_type_decl (tds, ods) d = (d.ty_name, d) :: tds, ods
let lookup_type_decl_op (tds, _) id = List.assoc_opt id tds

(* Assuption is that this is performed only after constant has been 
 * introduced *)
let lookup_type_decl (tds, _) id = List.assoc id tds
let is_type (tds, _) id = List.mem_assoc id tds

(* used to add a new object declaration and extend the relevant object 
 * list. We assume this will only be used when the appropriate type 
 * constant declaration already exists. *)
let add_obj_decl ((tds, ods) : signature) (d : obj_decl) =
  let ty_head_id = Term.get_ty_head d.typ in
  let tdecl = lookup_type_decl (tds, ods) ty_head_id in
  tdecl.objs <- d.obj_name :: tdecl.objs;
  tds, (d.obj_name, d) :: ods
;;

let lookup_obj_decl_op (_, ods) id = List.assoc_opt id ods

(* Assuption is that this is performed only after constant has been 
 * introduced *)
let lookup_obj_decl (_, ods) id = List.assoc id ods
let is_obj (_, ods) id = List.mem_assoc id ods
