(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015-2022  Inria (Institut National de Recherche
 *                          en Informatique et en Automatique)
 * Modifications made by Chase Johnson
 *)

module Ext = Extensions

type cell = unit -> unit
type snap = cell list

let __snappers : (unit -> unit -> unit) list ref = ref []
let __after_hooks : snap ref = ref []
let __before_hooks : snap ref = ref []

type hook_time =
  | BeforeReload
  | AfterReload

exception Killme

let add_hook ~time f =
  match time with
  | BeforeReload -> __before_hooks := f :: !__before_hooks
  | AfterReload -> __after_hooks := f :: !__after_hooks
;;

let run_hooks hooks = List.iter (fun f -> f ()) hooks

let rref x =
  let xr = ref x in
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some xr);
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some xr ->
      let y = !xr in
      fun () -> xr := y
  in
  __snappers := snap :: !__snappers;
  xr
;;

let table () =
  let ht = Hashtbl.create 19 in
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some ht);
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some ht ->
      let saved = Hashtbl.copy ht in
      fun () -> Ext.Hashtbl.assign ht saved
  in
  __snappers := snap :: !__snappers;
  ht
;;

let make ~copy ~assign x =
  let wx = Weak.create 1 in
  Weak.set wx 0 (Some x);
  let snap () =
    match Weak.get wx 0 with
    | None -> raise Killme
    | Some x ->
      let saved = copy x in
      fun () -> assign x saved
  in
  __snappers := snap :: !__snappers;
  x
;;

let snapshot () : snap =
  let snap, snappers =
    List.fold_left
      (fun (snap, snappers) next ->
        try next () :: snap, next :: snappers with
        | Killme -> snap, snappers)
      ([], [])
      !__snappers
  in
  __snappers := snappers;
  snap
;;

let reload (snap : snap) =
  run_hooks !__before_hooks;
  List.iter (fun f -> f ()) snap;
  run_hooks !__after_hooks
;;

module Undo = struct
  let stack : snap list ref = ref []
  let reset () = stack := []
  let push () = stack := snapshot () :: !stack

  let undo () =
    match !stack with
    | [] -> failwith "Nothing left to undo"
    | prev :: older ->
      reload prev;
      stack := older
  ;;

  let back n0 =
    let rec spin hist n =
      match hist, n with
      | here :: hist, 1 ->
        reload here;
        stack := hist
      | _ :: hist, n -> spin hist (n - 1)
      | [], _ -> failwith "Cannot go that far back!"
    in
    spin !stack n0
  ;;
end
