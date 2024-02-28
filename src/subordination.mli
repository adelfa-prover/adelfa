module Sig = Signature
module T = Term

type subordination_rel

val subordination_rel_to_list : subordination_rel -> (Sig.id * Sig.id list) list
val subordination_relation : Sig.signature -> subordination_rel
val subordinates : subordination_rel -> Sig.id -> Sig.id -> bool
