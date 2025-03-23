open Extensions

exception Reported_parse_error

type id = string
type pos = Lexing.position * Lexing.position

type uterm =
  | UConst of pos * id
  | ULam of pos * (pos * id * Type.ty option) * uterm
  | UPi of pos * (pos * id) * uterm * uterm
  | UApp of pos * uterm * uterm
  | UType of pos

let get_const_id utm =
  match utm with
  | UConst (_, id) -> id
  | ULam _ | UPi _ | UApp _ | UType _ -> bugf "Expected constant when getting id"
;;

let get_pos = function
  | UConst (p, _) | ULam (p, _, _) | UPi (p, _, _, _) | UApp (p, _, _) | UType p -> p
;;

let change_pos p = function
  | UConst (_, s) -> UConst (p, s)
  | ULam (_, s, tm) -> ULam (p, s, tm)
  | UPi (_, s, ty, b) -> UPi (p, s, ty, b)
  | UApp (_, t1, t2) -> UApp (p, t1, t2)
  | UType _ -> UType p
;;

let get_hid_and_args utm =
  let rec aux args = function
    | UConst (_, id) -> id, args
    | UApp (_, t1, t2) -> aux (t2 :: args) t1
    | _ -> bugf "Cannot get id and args of uterm"
  in
  aux [] utm
;;

type uctx =
  | UNil of pos
  | UVar of pos * id
  | UCtxTm of pos * uctx * (id * uterm)

type aid = id * Type.ty option

type uformula =
  | UTop
  | UBottom
  | UImp of uformula * uformula
  | UOr of uformula * uformula
  | UAnd of uformula * uformula
  | UAll of (pos * aid) list * uformula
  | UExists of (pos * aid) list * uformula
  | UCtx of (pos * id * id) list * uformula
  | UAtm of uctx * uterm * uterm * Formula.annotation
  | UProp of uterm

type uschema = ((pos * id) list * (pos * id * uterm) list) list
type udef = uformula * uformula

type clearable =
  | Keep of id
  | Remove of id

type uwith =
  | Cws of id * uctx
  | Vws of id * uterm

type depth =
  | DefaultDepth
  | WithDepth of int

type setting = SearchDepth of int

let is_cws = function
  | Cws _ -> true
  | _ -> false
;;

let is_vws = function
  | Vws _ -> true
  | _ -> false
;;

let unwrap_cws uw =
  match uw with
  | Cws (id, ctx) -> id, ctx
  | Vws _ -> bugf "Expected with context when unwrapping"
;;

let unwrap_vws uw =
  match uw with
  | Vws (id, tm) -> id, tm
  | Cws _ -> bugf "Expected with term when unwrapping"
;;

type common_command =
  | Undo
  | Set of setting list

type command =
  | Skip
  | Search of depth
  | Ind of int
  | Apply of clearable * clearable list * uwith list
  | Case of clearable
  | Exists of uterm
  | Split
  | Left
  | Right
  | Intros
  | Assert of uformula * depth
  | Abort
  | Weaken of clearable * uterm * depth
  | PermuteCtx of clearable * uctx
  | Permute of clearable * (id * id) list
  | Strengthen of clearable
  | Inst of clearable * uwith list * depth
  | Prune of id
  | Unfold of id option * uwith list
  | AppDfn of id * id option * uwith list
  | Common of common_command

type top_command =
  | Theorem of id * uformula
  | Schema of id * uschema
  | Specification of string
  | Quit
  | Define of aid * udef list
  | TopCommon of common_command

type sig_decl =
  | Const of id * uterm
  (* | Define of id * uterm option * uterm *)
  (* | Abbrev of id * uterm option * uterm *)
  | Fixity of id * Signature.fixity
(* | Name of id * id * id option *)
(* | Query of int * int * id option * uterm *)
(* | Clause of id * uterm option * uterm *)
(* | Solve of (id * id * uterm option) list * id option * uterm *)
(* | Tabled of id *)
(* | QueryTabled of int * int * id option * uterm *)
(* | Deterministic of id *)
(* | Mode of (mode * id * uterm option) list * uterm *)
(* | Terminates of order * callpat list *)
(* | Reduces of placeholder *)
(* | Block of id * (id * uterm option) list * (id * uterm option) *)
(* | Worlds of id list * callpat list *)
(* | Total of order * callpat list *)
(* | Freeze of id list *)
(* | Theorem of id * mform *)
(* | Prove of int * order * callpat list *)
(* | Establish of int * order * callpat list *)
(* | Assert of callpat list *)
(* | Use of id *)

let extract_unbound_uterm bvars utm =
  let rec aux bvars = function
    | UConst (_, id) -> if List.mem id bvars then [] else [ id ]
    | ULam (_, (_, id, _), utm) -> aux (id :: bvars) utm
    | UPi (_, (_, id), utma, utmm) -> aux bvars utma @ aux (id :: bvars) utmm
    | UApp (_, utml, utmr) -> aux bvars utml @ aux bvars utmr
    | UType _ -> []
  in
  List.unique (aux bvars utm)
;;

let extract_unbound_uctx bvars uctx =
  let rec aux = function
    | UNil _ | UVar _ -> []
    | UCtxTm (_, uctx, (_, utm)) -> aux uctx @ extract_unbound_uterm bvars utm
  in
  List.unique (aux uctx)
;;

let extract_unbound_uform bvars uform =
  let rec aux bvars = function
    | UTop | UBottom -> []
    | UImp (ufl, ufr) | UOr (ufl, ufr) | UAnd (ufl, ufr) -> aux bvars ufl @ aux bvars ufr
    | UAll (bndrs, uf) | UExists (bndrs, uf) ->
      aux (List.map (fun (_, (id, _)) -> id) bndrs @ bvars) uf
    | UCtx (_, uf) -> aux bvars uf
    | UAtm (uctx, utmm, utma, _) ->
      extract_unbound_uctx bvars uctx
      @ extract_unbound_uterm bvars utmm
      @ extract_unbound_uterm bvars utma
    | UProp utm -> extract_unbound_uterm bvars utm
  in
  List.unique (aux bvars uform)
;;

module Print = struct
  let pr_str ppf s = Format.fprintf ppf "%s" s

  let rec pr_uterm ppf = function
    | UConst (_, id) -> pr_str ppf id
    | ULam (_, (_, id, None), utm) ->
      Format.fprintf ppf "@[<2>[%a]@,%a@]" pr_str id pr_uterm utm
    | ULam (_, (_, id, Some ty), utm) ->
      Format.fprintf
        ppf
        "@[<2>[%a@ :@ %a]@,%a@]"
        pr_str
        id
        Type.Print.pr_ty
        ty
        pr_uterm
        utm
    | UPi (_, (_, id), uty, utm) ->
      Format.fprintf ppf "@[<2>{%a@,:@,%a}@,%a@]" pr_str id pr_uterm uty pr_uterm utm
    | UApp (_, utm1, (ULam _ as utm2)) ->
      Format.fprintf ppf "@[<2>%a@ (%a)@]" pr_uterm utm1 pr_uterm utm2
    | UApp (_, utm1, utm2) ->
      Format.fprintf ppf "@[<2>%a@ %a@]" pr_uterm utm1 pr_uterm utm2
    | UType _ -> pr_str ppf "type"
  ;;

  let rec pr_uctxtm ppf = function
    | UNil _ -> ()
    | UVar (_, id) -> pr_str ppf id
    | UCtxTm (_, UNil _, (id, utm)) -> Format.fprintf ppf "%a:%a" pr_str id pr_uterm utm
    | UCtxTm (_, uctx, (id, utm)) ->
      Format.fprintf ppf "%a,@,%a:%a" pr_uctxtm uctx pr_str id pr_uterm utm
  ;;

  let pr_uctx ppf = function
    | UNil _ -> ()
    | uctx -> Format.fprintf ppf "%a@ |-@ " pr_uctxtm uctx
  ;;

  let rec pr_uform ppf = function
    | UTop -> pr_str ppf "true"
    | UBottom -> pr_str ppf "false"
    | UImp (l, r) -> Format.fprintf ppf "@[<2>%a@ =>@ %a@]" pr_uform l pr_uform r
    | UOr (l, r) -> Format.fprintf ppf "@[<2>%a@ \\/@ %a@]" pr_uform l pr_uform r
    | UAnd (l, r) -> Format.fprintf ppf "@[<2>%a@ /\\@ %a@]" pr_uform l pr_uform r
    | UAll (locids, f) ->
      Format.fprintf ppf "@[<2>forall %a,@ %a@]" pr_locidtys locids pr_uform f
    | UExists (locids, f) ->
      Format.fprintf ppf "@[<2>exists %a,@ %a@]" pr_locidtys locids pr_uform f
    | UCtx (locctxs, f) ->
      Format.fprintf ppf "@[<2>ctx %a,@ %a@]" pr_locctxs locctxs pr_uform f
    | UAtm (uctx, utm, uty, ann) ->
      Format.fprintf
        ppf
        "@[<2>{@,%a@,%a@ :@ %a}%a"
        pr_uctx
        uctx
        pr_uterm
        utm
        pr_uterm
        uty
        Formula.Print.pr_ann
        ann
    | UProp utm -> pr_uterm ppf utm

  and pr_locctxs ppf = function
    | [] -> ()
    | (_, v, cty) :: locctx ->
      Format.fprintf ppf "@ %a:%a@,%a" pr_str v pr_str cty pr_locctxs locctx

  and pr_locidtys ppf = function
    | [] -> ()
    | (_, (id, None)) :: locidtys ->
      Format.fprintf ppf "@ %a@,%a" pr_str id pr_locidtys locidtys
    | (_, (id, Some ty)) :: locidtys ->
      Format.fprintf ppf "@ %a:%a@,%a" pr_str id Type.Print.pr_ty ty pr_locidtys locidtys
  ;;

  let rec pr_common ppf = function
    | Undo -> pr_str ppf "undo."
    | Set settings -> Format.fprintf ppf "@[<4>Set@ %a@.@]" pr_settings settings

  and pr_setting ppf = function
    | SearchDepth v -> Format.fprintf ppf "search_depth %a" pr_str (string_of_int v)

  and pr_settings ppf settings =
    match settings with
    | [] -> ()
    | [ v ] -> Format.fprintf ppf "%a" pr_setting v
    | s :: tl -> Format.fprintf ppf "%a, %a" pr_setting s pr_settings tl
  ;;

  let rec pr_perm ppf = function
    | [] -> ()
    | [ (n, n') ] -> Format.fprintf ppf "@[%a -> %a@]" pr_str n pr_str n'
    | (n, n') :: r -> Format.fprintf ppf "@[%a -> %a,@] %a" pr_str n pr_str n' pr_perm r
  ;;

  let rec pr_command ppf = function
    | Weaken (name, utm, DefaultDepth) ->
      Format.fprintf ppf "@[<4>weaken %a with %a.@]" pr_clearable name pr_uterm utm
    | Weaken (name, utm, WithDepth i) ->
      Format.fprintf
        ppf
        "@[<4>weaken %a with %a %a.@]"
        pr_clearable
        name
        pr_uterm
        utm
        pr_str
        (string_of_int i)
    | Abort -> pr_str ppf "abort."
    | Skip -> pr_str ppf "skip."
    | Search DefaultDepth -> pr_str ppf "search."
    | Search (WithDepth i) -> Format.fprintf ppf "search %a." pr_str (string_of_int i)
    | Ind i -> Format.fprintf ppf "induction on %a." pr_str (string_of_int i)
    | Apply (name, args, []) ->
      Format.fprintf ppf "@[<4>apply %a %a.@]" pr_clearable name pr_args args
    | Apply (name, args, withs) ->
      Format.fprintf
        ppf
        "@[<4>apply %a %a with %a.@]"
        pr_clearable
        name
        pr_args
        args
        pr_withs
        withs
    | Case name -> Format.fprintf ppf "cases %a." pr_clearable name
    | Exists utm -> Format.fprintf ppf "@[<4>exists %a.@]" pr_uterm utm
    | Split -> pr_str ppf "split."
    | Left -> pr_str ppf "left."
    | Right -> pr_str ppf "right."
    | Intros -> pr_str ppf "intros."
    | Assert (uform, DefaultDepth) ->
      Format.fprintf ppf "@[<4>assert %a.@]" pr_uform uform
    | Assert (uform, WithDepth i) ->
      Format.fprintf ppf "@[<4>assert %a %a.@]" pr_uform uform pr_str (string_of_int i)
    | PermuteCtx (name, uctx) ->
      Format.fprintf ppf "@[<4>ctxpermute %a to %a.@]" pr_clearable name pr_uctxtm uctx
    | Permute (name, perm) ->
      Format.fprintf ppf "@[<4>permute %a to %a.@]" pr_clearable name pr_perm perm
    | Strengthen name -> Format.fprintf ppf "strengthen %a." pr_clearable name
    | Inst (name, withs, DefaultDepth) ->
      Format.fprintf ppf "@[<4>inst %a with %a.@]" pr_clearable name pr_withs withs
    | Inst (name, withs, WithDepth i) ->
      Format.fprintf
        ppf
        "@[<4>inst %a with %a %a.@]"
        pr_clearable
        name
        pr_withs
        withs
        pr_str
        (string_of_int i)
    | Prune id -> Format.fprintf ppf "prune %a." pr_str id
    | Unfold (None, []) -> pr_str ppf "unfold."
    | Unfold (Some hid, []) -> Format.fprintf ppf "unfold %a." pr_str hid
    | Unfold (None, withs) -> Format.fprintf ppf "@[<4>unfold with %a.@]" pr_withs withs
    | Unfold (Some hid, withs) ->
      Format.fprintf ppf "@[<4>unfold %a with %a.@]" pr_str hid pr_withs withs
    | AppDfn (did, None, []) -> Format.fprintf ppf "appdfn %a." pr_str did
    | AppDfn (did, Some hid, []) ->
      Format.fprintf ppf "appdfn %a to %a." pr_str did pr_str hid
    | AppDfn (did, None, withs) ->
      Format.fprintf ppf "@[<4>appdfn %a with %a.@]" pr_str did pr_withs withs
    | AppDfn (did, Some hid, withs) ->
      Format.fprintf
        ppf
        "@[<4>appdfn %a to %a with %a.@]"
        pr_str
        did
        pr_str
        hid
        pr_withs
        withs
    | Common c -> pr_common ppf c

  and pr_clearable ppf = function
    | Keep id | Remove id -> pr_str ppf id

  and pr_clearablelist ppf = function
    | [] -> ()
    | [ clearable ] -> Format.fprintf ppf "%a" pr_clearable clearable
    | clearable :: clearables ->
      Format.fprintf ppf "%a@ %a" pr_clearable clearable pr_clearablelist clearables

  and pr_args ppf = function
    | [] -> ()
    | args -> Format.fprintf ppf "to@ %a" pr_clearablelist args

  and pr_with ppf = function
    | Vws (id, utm) -> Format.fprintf ppf "%a@ =@ %a" pr_str id pr_uterm utm
    | Cws (id, uctx) -> Format.fprintf ppf "(%a@ =@ %a)" pr_str id pr_uctxtm uctx

  and pr_withs ppf = function
    | [] -> ()
    | [ w ] -> pr_with ppf w
    | w :: withs -> Format.fprintf ppf "%a,@ %a" pr_with w pr_withs withs
  ;;

  let pr_aid ppf = function
    | id, Some ty -> Format.fprintf ppf "@[<2>%a@ :@ %a@]" pr_str id Type.Print.pr_ty ty
    | id, None -> pr_str ppf id
  ;;

  let pr_udef ppf (f1, f2) = Format.fprintf ppf "%a@ :=%a" pr_uform f1 pr_uform f2

  let rec pr_udefs ppf = function
    | [] -> ()
    | [ def ] -> pr_udef ppf def
    | def :: defs -> Format.fprintf ppf "%a;\n%a" pr_udef def pr_udefs defs
  ;;

  let rec pr_uschema ppf = function
    | [] -> ()
    | [ ublockschema ] -> Format.fprintf ppf "%a" pr_ublockschema ublockschema
    | ublockschema :: ublockschemas ->
      Format.fprintf ppf "%a;@ %a" pr_ublockschema ublockschema pr_uschema ublockschemas

  and pr_ublockschema ppf (locids, locentries) =
    Format.fprintf ppf "@[<4>{%a}@,(%a)@]" pr_locids locids pr_locentries locentries

  and pr_locentries ppf = function
    | [] -> ()
    | [ (_, name, ty) ] -> Format.fprintf ppf "%a:%a" pr_str name pr_uterm ty
    | (_, name, ty) :: locentries ->
      Format.fprintf ppf "%a:%a,@,%a" pr_str name pr_uterm ty pr_locentries locentries

  and pr_locids ppf = function
    | [] -> ()
    | [ (_, id) ] -> Format.fprintf ppf "%a" pr_str id
    | (_, id) :: locids -> Format.fprintf ppf "%a@,@ %a" pr_str id pr_locids locids
  ;;

  let pr_topcommand ppf = function
    | Theorem (name, uform) ->
      Format.fprintf ppf "@[<4>Theorem@ %a@,:@ %a.@]" pr_str name pr_uform uform
    | Schema (name, uschema) ->
      Format.fprintf ppf "@[<4>Schema@ %a@ :=@ %a.@]" pr_str name pr_uschema uschema
    | Specification name -> Format.fprintf ppf "@[<4>Specification@ %a.@]" pr_str name
    | Quit -> pr_str ppf "Quit."
    | Define (aid, defs) ->
      Format.fprintf ppf "@[<4>Define@ %a@ by\n%a.@]" pr_aid aid pr_udefs defs
    | TopCommon c -> pr_common ppf c
  ;;

  let rec pr_subst ppf = function
    | [] -> ()
    | (id, tm) :: subst ->
      Format.fprintf
        ppf
        "%a -> %a\n%a"
        pr_str
        id
        (Term.Print.pr_term [])
        tm
        pr_subst
        subst
  ;;

  let string_of_uterm ut =
    pr_uterm Format.str_formatter ut;
    Format.flush_str_formatter ()
  ;;

  let string_of_command command =
    pr_command Format.str_formatter command;
    Format.flush_str_formatter ()
  ;;

  let string_of_topcommand command =
    pr_topcommand Format.str_formatter command;
    Format.flush_str_formatter ()
  ;;
end
