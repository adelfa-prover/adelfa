(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015-2022  Inria (Institut National de Recherche
 *                          en Informatique et en Automatique)
 * Modifications made by Chase Johnson
 *)

val rref : 'a -> 'a ref
val table : unit -> ('a, 'b) Hashtbl.t
val make : copy:('a -> 'a) -> assign:('a -> 'a -> unit) -> 'a -> 'a

type hook_time =
  | BeforeReload
  | AfterReload

type snap

val snapshot : unit -> snap
val add_hook : time:hook_time -> (unit -> unit) -> unit
val reload : snap -> unit

module Undo : sig
  val reset : unit -> unit
  val undo : unit -> unit
  val push : unit -> unit
  val back : int -> unit
end
