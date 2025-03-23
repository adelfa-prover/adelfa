(*
 * TYPE
 * Representation of arity types.
 * 
 * This file defines the representation of arity types which is
 * the typing used in the logic.
 *)
type ty = Ty of ty list * string

let tyarrow tys ty =
  match ty with
  | Ty (tys', bty) -> Ty (tys @ tys', bty)
;;

let tybase bty = Ty ([], bty)
let oty = tybase "o"
let propty = tybase "prop"

let rec eq (Ty (tys1, bty1)) (Ty (tys2, bty2)) =
  try List.fold_left2 (fun t ty1 ty2 -> t && eq ty1 ty2) (bty1 = bty2) tys1 tys2 with
  | Invalid_argument _ -> false
;;

module Print = struct
  let pr_str ppf s = Format.fprintf ppf "%s" s

  let rec pr_ty_literal ppf = function
    | Ty (tys, bty) -> Format.fprintf ppf "Ty([%a],%a)" pr_tylst_literal tys pr_str bty

  and pr_tylst_literal ppf = function
    | [] -> ()
    | [ ty ] -> pr_ty_literal ppf ty
    | ty :: tys -> Format.fprintf ppf "%a,@ %a" pr_ty_literal ty pr_tylst_literal tys
  ;;

  let string_of_ty_literal ty =
    pr_ty_literal Format.str_formatter ty;
    Format.flush_str_formatter ()
  ;;

  (*** These first functions will print LF terms in fully explicit form. They do not use the
    signature to determine implicit arguments or fixity. ***)
  let rec pr_ty ppf = function
    | Ty (tys, bty) ->
      let rec pr_tys ppf tys =
        match tys with
        | [] -> pr_str ppf bty
        | arg :: tys' ->
          Format.fprintf ppf "@[<2>(%a)@ %a@ %a@]" pr_ty arg pr_str "->" pr_tys tys'
      in
      pr_tys ppf tys
  ;;

  let string_of_ty ty =
    pr_ty Format.str_formatter ty;
    Format.flush_str_formatter ()
  ;;
end
