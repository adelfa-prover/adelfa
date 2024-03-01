module Sig = Signature
module T = Term

type sub_rel

val empty : sub_rel

(** [sub_rel_to_list sub_rel] returns a list of pairs [(a, [b1; b2; ...; bn])]
    where [a] is a type name and [b1; b2; ...; bn] are the type names which
    a subordinates. *)
val sub_rel_to_list : sub_rel -> (Sig.id * Sig.id list) list

(** [sub_relation signature] returns a new {!sub_rel} for the
    {!type:Signature.signature} *)
val sub_relation : Sig.signature -> sub_rel

(** [subordinates sub_rel a b] returns true if the type name [a] is subordinate
    to [b]. *)
val subordinates : sub_rel -> Sig.id -> Sig.id -> bool
