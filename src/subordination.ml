module Sig = Signature
module T = Term

(* NOTE: The subordination checks use associative lists and don't fill
   transitive connections -- making lookup possibly expensive. If this causes a
   slowdown, think about using sets and/or filling any transitive connections
   to allow [has_path] to only look at the single entry. *)
type key = Sig.id
type value = Sig.id list
type entry = key * value
type sub_rel = entry list

module Graph = struct
  let empty : sub_rel = []

  let rec get_opt (graph : sub_rel) (node : key) : value option =
    match graph with
    | [] -> None
    | (n, x) :: _ when n = node -> Some x
    | _ :: tl -> get_opt tl node
  ;;

  let has_path (graph : sub_rel) (from_node : key) (to_node : key) : bool =
    let rec aux visited graph node =
      if List.mem node visited
      then false
      else (
        match get_opt graph node with
        | None -> false
        | Some x when List.mem to_node x -> true
        | Some x -> List.exists (aux (node :: visited) graph) x)
    in
    aux [] graph from_node
  ;;

  let insert (graph : sub_rel) (src : key) (dst : key) : sub_rel =
    let rec aux graph src dst =
      match graph with
      | [] -> [ src, [ dst ] ]
      | (n, x) :: tl when n = src -> (n, dst :: x) :: tl
      | h :: tl -> h :: aux tl src dst
    in
    if has_path graph src dst then graph else aux graph src dst
  ;;
end

let sub_rel_to_list rel = rel

let add_term_to_graph (graph : sub_rel) (name : Sig.id) (term : T.term)
  : sub_rel
  =
  let rec aux term =
    match T.observe (T.hnorm term) with
    | T.Type -> [ name ]
    (* | T.Var n -> [ n.name ] *)
    | T.Lam (_, t) -> aux t
    | T.Pi (bndrs, t) ->
      List.append (List.map (fun (_, x) -> Term.get_ty_head x) bndrs) (aux t)
    | T.App (f, x) -> List.append (aux f) (List.map aux x |> List.flatten)
    | _ -> []
  in
  List.fold_left (fun graph node -> Graph.insert graph node name) graph (aux term)
;;

let add_type_to_graph (graph : sub_rel) (type_decl : Sig.type_decl)
  : sub_rel
  =
  let name = type_decl.Sig.ty_name in
  let term = type_decl.Sig.kind in
  add_term_to_graph graph name term
;;

let add_obj_to_graph (graph : sub_rel) (obj_decl : Sig.obj_decl)
  : sub_rel
  =
  let term = obj_decl.Sig.typ in
  let type_name = Term.get_ty_head obj_decl.Sig.typ in
  add_term_to_graph graph type_name term
;;

let sub_relation (signature : Sig.signature) : sub_rel =
  let type_graph =
    Sig.get_type_decls signature |> List.fold_left add_type_to_graph Graph.empty
  in
  Sig.get_obj_decls signature |> List.fold_left add_obj_to_graph type_graph

let subordinates (rel : sub_rel) (a : Sig.id) (b : Sig.id) =
  Graph.has_path rel a b
;;
