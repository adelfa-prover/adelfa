(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

let ( >> ) f g x = g (f x)
let ( << ) f g x = f (g x)
let curry f (x, y) = f x y
let uncurry f x y = f (x, y)
let failwithf fmt = Printf.ksprintf failwith fmt
let bugf fmt = Printf.ksprintf failwith @@ "[ADELFA ERROR]\n" ^^ fmt
let return x = Some x

let ( let* ) o f =
  match o with
  | None -> None
  | Some x -> f x
;;

let maybe_guard ?guard f =
  match guard with
  | None -> f
  | Some g -> g f
;;

module Option = struct
  let is_some x =
    match x with
    | Some _ -> true
    | None -> false
  ;;

  let is_none x =
    match x with
    | Some _ -> false
    | None -> true
  ;;

  let get x =
    match x with
    | Some v -> v
    | None -> failwith "Option.get called on None"
  ;;

  let map_default f default x =
    match x with
    | Some v -> f v
    | None -> default
  ;;

  let default default x =
    match x with
    | Some v -> v
    | None -> default
  ;;
end

module String = struct
  include String

  let count str char =
    let count = ref 0 in
    String.iter (fun c -> if c = char then incr count) str;
    !count
  ;;
end

module List = struct
  include List

  let mem ?(cmp = ( = )) elt list =
    let rec aux list =
      match list with
      | [] -> false
      | head :: tail -> cmp elt head || aux tail
    in
    aux list
  ;;

  let remove ?(cmp = ( = )) elt list =
    let rec aux list =
      match list with
      | [] -> []
      | head :: tail when cmp elt head -> aux tail
      | head :: tail -> head :: aux tail
    in
    aux list
  ;;

  let unique ?(cmp = ( = )) list =
    let rec aux list =
      match list with
      | [] -> []
      | head :: tail -> head :: aux (remove ~cmp head tail)
    in
    aux list
  ;;

  let is_unique ?(cmp = ( = )) list =
    let rec aux list =
      match list with
      | [] -> true
      | head :: tail -> (not (mem ~cmp head tail)) && aux tail
    in
    aux list
  ;;

  let find_duplicate list =
    let rec aux list =
      match list with
      | [] -> None
      | head :: tail when mem head tail -> Some head
      | _ :: tail -> aux tail
    in
    aux list
  ;;

  let find_duplicates list =
    let rec aux list =
      match list with
      | [] -> []
      | head :: tl when mem head tl -> head :: aux tl
      | _ :: tl -> aux tl
    in
    aux list
  ;;

  let map ?guard f list = map (maybe_guard ?guard f) list
  let iter ?guard f list = iter (maybe_guard ?guard f) list
  let find_all ?guard f list = filter (maybe_guard ?guard f) list

  let find_some ?guard f list =
    let f = maybe_guard ?guard f in
    let rec aux list =
      match list with
      | [] -> None
      | head :: tail ->
        (match f head with
         | Some v -> Some v
         | None -> aux tail)
    in
    aux list
  ;;

  let filter_map ?guard f list =
    let f = maybe_guard ?guard f in
    map Option.get (find_all Option.is_some (map f list))
  ;;

  let flatten_map ?guard f list =
    let f = maybe_guard ?guard f in
    flatten (map f list)
  ;;

  let remove_all ?guard f list =
    let f = maybe_guard ?guard f in
    find_all (fun x -> not (f x)) list
  ;;

  let minus ?(cmp = ( = )) list1 list2 = remove_all (fun e -> mem ~cmp e list2) list1
  let intersect ?(cmp = ( = )) list1 list2 = find_all (fun e -> mem ~cmp e list2) list1

  let rec take n list =
    match list, n with
    | [], _ -> []
    | _, n when n <= 0 -> []
    | x :: xs, n -> x :: take (n - 1) xs
  ;;

  let remove_assocs to_remove alist =
    let rec aux alist =
      match alist with
      | (a, b) :: rest -> if mem a to_remove then aux rest else (a, b) :: aux rest
      | [] -> []
    in
    aux alist
  ;;

  let assoc_all ?(cmp = ( = )) x list =
    let rec aux list =
      match list with
      | [] -> []
      | (a, b) :: tail when cmp x a -> b :: aux tail
      | _ :: tail -> aux tail
    in
    aux list
  ;;

  let remove_all_assoc ?(cmp = ( = )) x list =
    let rec aux list =
      match list with
      | [] -> []
      | (a, _) :: tail when cmp x a -> aux tail
      | head :: tail -> head :: aux tail
    in
    aux list
  ;;

  let collate_assoc ?(cmp = ( = )) alist =
    let rec spin finished ck cv = function
      | [] -> List.rev ((ck, List.rev cv) :: finished)
      | (nk, nv) :: rest ->
        if cmp ck nk
        then spin finished ck (nv :: cv) rest
        else spin ((ck, List.rev cv) :: finished) nk [ nv ] rest
    in
    match alist with
    | [] -> []
    | (nk, nv) :: rest -> spin [] nk [ nv ] rest
  ;;

  let index_of ?(cmp = ( = )) v l =
    let rec aux l =
      match l with
      | [] -> invalid_arg "value not in list"
      | x :: xs -> if cmp x v then 0 else 1 + aux xs
    in
    aux l
  ;;

  let max list =
    let rec aux list m =
      match list with
      | [] -> m
      | head :: tail -> aux tail (max head m)
    in
    aux list 0
  ;;

  let rec distribute elt list =
    match list with
    | [] -> [ [ elt ] ]
    | head :: tail -> (elt :: list) :: map (fun x -> head :: x) (distribute elt tail)
  ;;

  (* Generate all permutations of all n element subsets of list *)
  let rec permute n list =
    if n = 0
    then [ [] ]
    else (
      match list with
      | [] -> []
      | head :: tail ->
        flatten_map (distribute head) (permute (n - 1) tail) @ permute n tail)
  ;;

  (* Generate all n element subsets of list *)
  let rec choose n list =
    if n = 0
    then [ [] ]
    else (
      match list with
      | [] -> []
      | head :: tail -> map (fun t -> head :: t) (choose (n - 1) tail) @ choose n tail)
  ;;

  let rec range a b = if a > b then [] else a :: range (a + 1) b

  let number list =
    let rec aux i list =
      match list with
      | [] -> []
      | head :: tail -> (i, head) :: aux (i + 1) tail
    in
    aux 1 list
  ;;

  let fold_left1 f list =
    match list with
    | x :: xs -> fold_left f x xs
    | _ -> invalid_arg "Empty list"
  ;;

  let rec drop n list =
    match list with
    | _ :: xs when n > 0 -> drop (n - 1) xs
    | _ -> list
  ;;

  let drop_last n list = rev (drop n (rev list))
  let take_last n list = rev (take n (rev list))

  let rec last = function
    | [] -> invalid_arg "List.last"
    | [ x ] -> x
    | _ :: l -> last l
  ;;

  let rev_map f list =
    let rec aux list acc =
      match list with
      | [] -> acc
      | x :: xs -> aux xs (f x :: acc)
    in
    aux list []
  ;;

  let rec rev_app xs ys =
    match xs with
    | [] -> ys
    | x :: xs -> rev_app xs (x :: ys)
  ;;

  let replicate n x =
    let rec aux = function
      | 0 -> []
      | i -> x :: aux (i - 1)
    in
    aux n
  ;;

  let map_fst f list = map (fun (x, y) -> f x, y) list
  let map_snd f list = map (fun (x, y) -> x, f y) list

  let rec combine3 l1 l2 l3 =
    match l1, l2, l3 with
    | [], [], [] -> []
    | x :: xs, y :: ys, z :: zs -> (x, y, z) :: combine3 xs ys zs
    | _ -> raise (Invalid_argument "List.combine3")
  ;;

  let rec combine_shortest l1 l2 =
    match l1, l2 with
    | [], _ | _, [] -> []
    | x :: xs, y :: ys -> (x, y) :: combine_shortest xs ys
  ;;

  let subset l1 l2 = List.for_all (fun v -> List.mem v l2) l1
end

module Hashtbl = struct
  include Hashtbl

  let assign dest src =
    clear dest;
    iter (fun a b -> add dest a b) src
  ;;

  let remove_all f tbl =
    let f' k v = if f k v then None else Some v in
    Hashtbl.filter_map_inplace f' tbl
  ;;

  let to_list tbl = Hashtbl.to_seq tbl |> List.of_seq
end

module Either = struct
  type ('a, 'b) either =
    | Left of 'a
    | Right of 'b

  let either left right e =
    match e with
    | Left x -> left x
    | Right x -> right x
  ;;

  let partition_eithers eithers =
    let left x (l, r) = x :: l, r in
    let right x (l, r) = l, x :: r in
    List.fold_right (either left right) eithers ([], [])
  ;;
end

module Seq = struct
  include Seq

  let uncons s =
    match s () with
    | Cons (x, xs) -> Some (x, xs)
    | Nil -> None
  ;;

  let rec distribute elt (seq : 'a Seq.t) : 'a Seq.t Seq.t =
    match uncons seq with
    | None -> Seq.return elt |> Seq.return
    | Some (head, tail) ->
      Seq.cons
        (Seq.cons elt seq)
        (Seq.map (fun x -> Seq.cons head x) (distribute elt tail))
  ;;

  (* Generate all permutations of all n element subsets of the sequence *)
  let rec permute (n : int) (seq : 'a Seq.t) =
    if n = 0
    then Seq.return Seq.empty
    else (
      match uncons seq with
      | None -> Seq.empty
      | Some (head, rest) ->
        let with_head = Seq.flat_map (distribute head) (permute (n - 1) rest) in
        let without_head = permute n rest in
        Seq.append with_head without_head)
  ;;
end
