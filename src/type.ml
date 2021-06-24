(*
 * TYPE
 * Representation of arity types.
 * 
 * This file defines the representation of arity types which is
 * the typing used in the logic.
 *) 
type ty =
  | Ty of ty list * string

let tyarrow tys ty =
  match ty with
  | Ty(tys', bty) -> Ty(tys @ tys', bty)

let tybase bty = Ty([], bty)

let oty = tybase "o"
let propty = tybase "prop"
                 
let rec eq (Ty(tys1, bty1)) (Ty(tys2, bty2)) =
  try
    List.fold_left2 (fun t ty1 ty2 -> t && eq ty1 ty2) (bty1 = bty2) tys1 tys2
  with
  | Invalid_argument _ -> false
