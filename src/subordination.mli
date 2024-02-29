module Sig = Signature
module T = Term

type sub_rel

val sub_rel_to_list : sub_rel -> (Sig.id * Sig.id list) list
val sub_relation : Sig.signature -> sub_rel
val subordinates : sub_rel -> Sig.id -> Sig.id -> bool
