type elem = Term.t

module VS = Set.Make (Term)

type t = VS.t

let empty = VS.empty
let to_list s = VS.to_seq s |> List.of_seq
let is_empty s = VS.is_empty s
let to_id_list s = VS.to_seq s |> Seq.map (fun x -> x.Term.name) |> List.of_seq
let to_term_list s = VS.to_seq s |> Seq.map (fun x -> Term.var_to_term x) |> List.of_seq

let from_list elems =
  let s = empty in
  let elems = List.to_seq elems in
  VS.add_seq elems s
;;

let subset s1 s2 = VS.subset s1 s2
let mem s v = VS.mem v s
let union s1 s2 = VS.union s1 s2
let minus s1 s2 = VS.diff s1 s2
let filter f s = VS.filter f s
let add_var s v = VS.add v s
let add_term s t = VS.add (Term.term_to_var t) s
let add_vars s vs = VS.add_seq (List.to_seq vs) s
let copy s = s
