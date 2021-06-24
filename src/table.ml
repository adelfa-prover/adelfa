(** Provides an implementation of symbol tables. *)

(** Describe an ordering for {!Symb.symbol}. *)
module OrderedType =
struct
  type t = Symbol.symbol

  (** Order using less-than on integer identifier from symbol. *)
  let compare s1 s2 =
    let id1 = Symbol.id s1 in
    let id2 = Symbol.id s2 in
    if (id1 < id2) 
      then -1    
      else if (id1 > id2)
      then 1
      else 0
end

module Table = Map.Make(OrderedType)

type 'a table = 'a Table.t

let empty = Table.empty

let insert table key v = Table.add key v table

let lookup table key = 
  try
    Some(Table.find key table)
  with
    Not_found -> None

let remove table key = Table.remove key table

let fold table f v = Table.fold f table v

let iter table f = Table.iter f table
