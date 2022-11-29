type elem = Term.t
type t

val empty : t
val to_list : t -> elem list
val is_empty : t -> bool
val to_id_list : t -> string list
val to_term_list : t -> Term.term list
val from_list : elem list -> t
val add_var : t -> elem -> t
val add_vars : t -> elem list -> t
val add_term : t -> Term.term -> t
val filter : (elem -> bool) -> t -> t
val copy : t -> t
val mem : t -> elem -> bool
val union : t -> t -> t
val minus : t -> t -> t
