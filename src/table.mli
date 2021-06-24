(** Provides an implementation of symbol tables. *)

(** The type of tables. *)
type 'a table 

(** Construct an empty table. *)
val empty : 'a table

(** Insert an item into a table. *)
val insert : 'a table -> Id.id -> 'a -> 'a table

(** Find an item in a table. *)
val lookup : 'a table -> Id.id -> 'a option

(** Remove an item from a table. *)
val remove : 'a table -> Id.id -> 'a table

(** Apply a function to each item in a table. *)
val fold : 'a table -> (Id.id -> 'a -> 'b -> 'b) -> 'b -> 'b

(** Apply a function to each item in a table. *)
val iter : 'a table -> (Id.id -> 'a -> unit) -> unit
