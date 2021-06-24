(*
 *
 * SIGNATURE
 * Representation of LF Signature declarations.
 * 
 *)

type id = string

type associativity =
    None
  | Right
  | Left

type fixity =
    Infix of associativity * int
  | Prefix of int
  | Postfix of int
  | NoFixity

type type_decl = {
  name:id ;
  kind:Term.term;
  implicit:int;
  fix:fixity;
  mutable objs:id list
}
and obj_decl = {
  name:id;
  typ:Term.term;
  implicit:int;
  fix:fixity;
}
let ty_dec n k i f os = {name=n; kind=k; implicit=i; fix=f; objs=os}
let obj_dec n t i f = {name=n; typ=t; implicit=i; fix=f}

let add_obj_to_ty td id =
  td.objs <- id::td.objs
       
type signature = (id * type_decl) list * ((id * obj_decl) list)
let empty = ([],[])
  
let get_type_decls (tds,_) = List.map snd tds
let get_obj_decls (_,ods) = List.map snd ods

                                                  
let add_type_decl (tds,ods)  d =
  ((d.name,d)::tds,ods)
let lookup_type_decl_op (tds,_) id = List.assoc_opt id tds
(* Assuption is that this is performed only after constant has been 
 * introduced *)
let lookup_type_decl (tds,_) id = List.assoc id tds
let is_type (tds,ods) id =
  List.mem_assoc id tds
                                                       
(* used to add a new object declaration and extend the relevant object 
 * list. We assume this will only be used when the appropriate type 
 * constant declaration already exists. *)
let add_obj_decl ((tds, ods):signature) (d:obj_decl) =
  let ty_head_id = Term.get_ty_head d.typ in
  let tdecl = lookup_type_decl (tds,ods) ty_head_id in
  tdecl.objs <- (d.name :: tdecl.objs);
  (tds, ((d.name,d)::ods))
let lookup_obj_decl_op (_,ods) id = List.assoc_opt id ods 
(* Assuption is that this is performed only after constant has been 
 * introduced *)
let lookup_obj_decl (_,ods) id = List.assoc id ods
let is_obj (tds,ods) id =
  List.mem_assoc id ods
