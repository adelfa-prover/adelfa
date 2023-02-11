open Type
open Term
open Extensions

(* use ocaml formatting to print LF terms more nicely *)

let imp = "->"
let typekwd = "type"
let topkwd = "True"
let bottomkwd = "False"
let andkwd = "/\\"
let orkwd = "\\/"
let pr_str ppf s = Format.fprintf ppf "%s" s

let rec pr_strlst ppf = function
  | [] -> ()
  | [ s ] -> pr_str ppf s
  | s :: lst -> Format.fprintf ppf "%a,@ %a" pr_str s pr_strlst lst
;;

(*** These first functions will print LF terms in fully explicit form.
     They do not use the signature to determine implicit arguments or fixity. ***)

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

let rec pr_ty ppf = function
  | Ty (tys, bty) ->
    let rec pr_tys ppf tys =
      match tys with
      | [] -> pr_str ppf bty
      | arg :: tys' ->
        Format.fprintf ppf "@[<2>(%a)@ %a@ %a@]" pr_ty arg pr_str imp pr_tys tys'
    in
    pr_tys ppf tys
;;

let pr_var ppf v = pr_str ppf v.name
(* Format.fprintf ppf "(%a:%a)" pr_str v.name pr_ty v.ty *)

(* from DB printing in Abella *)
let abs_name = "x"

let db_to_string cx0 i0 =
  let rec spin cx i =
    match cx, i with
    | [], _ -> abs_name ^ string_of_int (i0 - List.length cx0 + 1)
    | name :: _, 1 -> name
    | _ :: cx, _ -> spin cx (i - 1)
  in
  spin cx0 i0
;;

let rec pr_term_literal ppf t =
  match t with
  | Var v -> Format.fprintf ppf "@[<2>Var(@,%a@,)@]" pr_var_literal v
  | DB i -> Format.fprintf ppf "@[<2>DB(@,%a@,)@]" pr_str (string_of_int i)
  | Lam (idtys, tm) ->
    Format.fprintf ppf "@[<2>Lam(@,[%a],@,%a)@]" pr_idlst idtys pr_term_literal tm
  | App (h, tms) ->
    Format.fprintf ppf "@[<2>App(@,%a,@,[%a]@,)@]" pr_term_literal h pr_tmlst tms
  | Pi (lfidtys, tm) ->
    Format.fprintf ppf "@[<2>Pi(@,[%a],@,%a)@]" pr_lfidlst lfidtys pr_term_literal tm
  | Type -> pr_str ppf "Type"
  | Ptr p -> Format.fprintf ppf "@[<2>Ptr(@,%a@,)@]" pr_ptr_literal p
  | Susp _ -> pr_term_literal ppf (hnorm t)

and pr_var_literal ppf v =
  let string_of_tag = function
    | Eigen -> "Eigen"
    | Constant -> "Constant"
    | Logic -> "Logic"
    | Nominal -> "Nominal"
  in
  Format.fprintf
    ppf
    "name=%a,@,tag=%a,@,ts=%a,@,ty=%a"
    pr_str
    v.name
    pr_str
    (string_of_tag v.tag)
    pr_str
    (string_of_int v.ts)
    pr_ty_literal
    v.ty

and pr_ptr_literal ppf p =
  match !p with
  | V v -> Format.fprintf ppf "V(@,Var(%a))" pr_var_literal v
  | T t -> Format.fprintf ppf "T(@,%a)" pr_term_literal t

and pr_lfidlst ppf lfidtys =
  match lfidtys with
  | [] -> Format.fprintf ppf "@,"
  | [ (v, ty) ] -> Format.fprintf ppf "@,(%a,%a)@," pr_str v.Term.name pr_term_literal ty
  | (v, ty) :: lfidtys' ->
    Format.fprintf
      ppf
      "@,(%a,%a)@,,%a"
      pr_str
      v.Term.name
      pr_term_literal
      ty
      pr_lfidlst
      lfidtys'

and pr_idlst ppf idtys =
  match idtys with
  | [] -> Format.fprintf ppf "@,"
  | [ (id, ty) ] -> Format.fprintf ppf "%a:%a" pr_str id pr_ty_literal ty
  | (id, ty) :: idtys' ->
    Format.fprintf ppf "%a:%a;@, %a" pr_str id pr_ty_literal ty pr_idlst idtys'

and pr_tmlst ppf tms =
  match tms with
  | [] -> Format.fprintf ppf "@,"
  | [ tm ] -> pr_term_literal ppf tm
  | tm :: tms' -> Format.fprintf ppf "%a;@, %a" pr_term_literal tm pr_tmlst tms'
;;

let string_of_term_literal tm =
  pr_term_literal Format.str_formatter tm;
  Format.flush_str_formatter ()
;;

let rec pr_term cx ppf t =
  match observe (hnorm t) with
  | Var v -> pr_var ppf v
  | DB i -> pr_db cx ppf i
  | Lam (idtys, tm) -> pr_lam cx ppf idtys tm
  | App (h, tms) -> pr_app cx ppf h tms
  | Pi (idtys, tm) -> pr_pi cx ppf idtys tm
  | Type -> pr_str ppf typekwd
  | _ -> assert false

and pr_term' cx ppf t =
  match observe (hnorm t) with
  | Var v -> pr_var ppf v
  | DB i -> pr_db cx ppf i
  | Lam (idtys, tm) -> Format.fprintf ppf "(%a)" (fun ppf -> pr_lam cx ppf idtys) tm
  | App _ -> Format.fprintf ppf "(%a)" (pr_term cx) t
  | Pi (idtys, tm) -> pr_pi cx ppf idtys tm
  | Type -> pr_str ppf typekwd
  | _ -> assert false

and pr_db cx ppf i = pr_str ppf (db_to_string cx i)

and pr_app cx ppf h tms =
  let rec pr_args ppf tms =
    match tms with
    | [] -> ()
    | t :: tms' -> Format.fprintf ppf "@ %a%a" (pr_term' cx) t pr_args tms'
  in
  Format.fprintf ppf "@[<hov 2>%a%a@]" (pr_term cx) h pr_args tms

and pr_lam cx ppf idtys tm =
  let rec pr_bndr cx ppf idtys =
    match idtys with
    | [] -> pr_term cx ppf tm
    | (n, _) :: idtys' ->
      Format.fprintf ppf "@[<2>[@,%a@,]%a@]" pr_str n (pr_bndr (n :: cx)) idtys'
  in
  pr_bndr cx ppf idtys

and pr_pi cx ppf idtys tm =
  let rec pr_bndr cx ppf idtys =
    match idtys with
    | [] -> pr_term cx ppf tm
    | (v, k) :: idtys' ->
      Format.fprintf
        ppf
        "@[<2>{@,%a@,:@,%a@,}%a@]"
        pr_var
        v
        (pr_term cx)
        k
        (pr_bndr (v.name :: cx))
        idtys'
  in
  pr_bndr cx ppf idtys
;;

let rec pr_varlst ppf lst =
  match lst with
  | [] -> ()
  | [ (id, t) ] -> Format.fprintf ppf "%a@,:@,%a" pr_str id pr_ty (Term.get_var_ty t)
  (* pr_str ppf id *)
  | (id, t) :: vs ->
    Format.fprintf ppf "%a@,:@,%a,@ %a" pr_str id pr_ty (Term.get_var_ty t) pr_varlst vs
;;

(* Format.fprintf ppf "%a,@ %a" pr_str id pr_varlst vs *)

let pr_ctxvar ppf v = pr_str ppf v

let rec pr_block ppf b =
  match b with
  | [] -> ()
  | [ (v, tm) ] -> Format.fprintf ppf "%a@,:@,%a" pr_str v.name (pr_term []) tm
  | (v, tm) :: b' ->
    Format.fprintf ppf "%a@,:@,%a,@ %a" pr_str v.name (pr_term []) tm pr_block b'
;;

let rec pr_blocks ppf blocks =
  match blocks with
  | [] -> ()
  | [ b ] -> Format.fprintf ppf "(%a)" pr_block b
  | b :: blocks' -> Format.fprintf ppf "%a,@ (%a)" pr_block b pr_blocks blocks'
;;

let pr_ctxty ppf (Context.CtxTy (id, blocks)) =
  Format.fprintf ppf "%a[%a]" pr_str id pr_blocks blocks
;;

let pr_ctxvarlst ppf (ctx : Context.CtxVarCtx.t) =
  let lst =
    Context.CtxVarCtx.to_list ctx
    |> List.map (fun (v, (n, b)) -> v, (VarSet.to_id_list !n, b))
  in
  let rec aux ppf lst =
    match lst with
    | [] -> ()
    | [ (id, (ns, ty)) ] ->
      Format.fprintf ppf "%a{%a}@,:@,%a" pr_str id pr_strlst ns pr_ctxty ty
    | (id, (ns, ty)) :: vs ->
      Format.fprintf ppf "%a{%a}@,:@,%a,@ %a" pr_str id pr_strlst ns pr_ctxty ty aux vs
  in
  aux ppf lst
;;

let pr_ann ppf = function
  | Formula.None -> ()
  | Formula.EQ i -> pr_str ppf (String.make i '@')
  | Formula.LT i -> pr_str ppf (String.make i '*')
;;

let pr_ctxentry ppf (v, tm) = Format.fprintf ppf "%a@,:@,%a" pr_var v (pr_term []) tm

let rec pr_ctxexpr ppf = function
  | Context.Nil -> ()
  | Context.Var v -> pr_ctxvar ppf v
  | Context.Ctx (Context.Nil, entry) -> pr_ctxentry ppf entry
  | Context.Ctx (ctx, entry) ->
    Format.fprintf ppf "%a,@ %a" pr_ctxexpr ctx pr_ctxentry entry
;;

let rec pr_ctxbndrs ppf bndrs =
  match bndrs with
  | [] -> ()
  | (n, schema) :: bndrs' ->
    Format.fprintf ppf "ctx %a@,:@,%a,@ %a" pr_str n pr_str schema pr_ctxbndrs bndrs'
;;

let rec pr_allbndrs ppf bndrs =
  match bndrs with
  | [] -> ()
  | (n, _) :: bndrs' -> Format.fprintf ppf "forall %a,@ %a" pr_str n pr_allbndrs bndrs'
;;

let rec pr_existsbndrs ppf bndrs =
  match bndrs with
  | [] -> ()
  | (n, _) :: bndrs' -> Format.fprintf ppf "exists %a,@ %a" pr_str n pr_existsbndrs bndrs'
;;

let rec pr_formula ppf = function
  | Formula.Top -> pr_str ppf topkwd
  | Formula.Bottom -> pr_str ppf bottomkwd
  | Formula.Atm (Context.Nil, m, a, ann) ->
    Format.fprintf ppf "@[<2>{%a@ :@ %a}%a@]" (pr_term []) m (pr_term []) a pr_ann ann
  | Formula.Atm (g, m, a, ann) ->
    Format.fprintf
      ppf
      "@[<2>{%a@,@ |-@ @,%a@ :@ %a}%a@]"
      pr_ctxexpr
      g
      (pr_term [])
      m
      (pr_term [])
      a
      pr_ann
      ann
  | Formula.Ctx (bndrs, f) ->
    Format.fprintf ppf "@[<2>%a%a@]" pr_ctxbndrs bndrs pr_formula f
  | Formula.All (bndrs, f) ->
    Format.fprintf ppf "@[<2>%a%a@]" pr_allbndrs bndrs pr_formula f
  | Formula.Exists (bndrs, f) ->
    Format.fprintf ppf "@[<2>%a%a@]" pr_existsbndrs bndrs pr_formula f
  | Formula.Imp (f1, f2) ->
    Format.fprintf ppf "@[<4>%a@ =>@ %a@]" pr_formula f1 pr_formula f2
  | Formula.And (f1, f2) ->
    Format.fprintf ppf "@[<4>%a@ %a@ %a@]" pr_formula f1 pr_str andkwd pr_formula f2
  | Formula.Or (f1, f2) ->
    Format.fprintf ppf "@[<4>%a@ %a@ %a@]" pr_formula f1 pr_str orkwd pr_formula f2
  | Formula.Prop (h, argtms) ->
    Format.fprintf ppf "@[<3>%a%a@]" pr_str h pr_propargs argtms

and pr_typing_judgement ppf = function
  | Formula.Atm (g, m, a, ann) ->
    Format.fprintf
      ppf
      "@[<2>%a@,@ |-@ @,%a@ :@ %a%a@]"
      pr_ctxexpr
      g
      (pr_term [])
      m
      (pr_term [])
      a
      pr_ann
      ann
  | f -> pr_formula ppf f

and pr_propargs ppf = function
  | [] -> ()
  | arg :: args' -> Format.fprintf ppf "@ %a%a" (pr_term []) arg pr_propargs args'
;;

let pr_hyp ppf hyp =
  if hyp.Sequent.tag = Sequent.Explicit
  then Format.fprintf ppf "%a:@,%a" pr_str hyp.Sequent.id pr_formula hyp.Sequent.formula
  else ()
;;

let rec pr_hyps ppf hyps =
  match hyps with
  | [] -> ()
  | h :: hyps' -> Format.fprintf ppf "@[<4>%a@]@.%a" pr_hyp h pr_hyps hyps'
;;

let pr_sequent ppf seq =
  if seq.Sequent.name = ""
  then Format.fprintf ppf "@\n"
  else Format.fprintf ppf "Subgoal %s:@\n@\n" seq.Sequent.name;
  let nvars = List.filter (fun (_, t) -> Term.is_var Term.Nominal t) seq.Sequent.vars in
  let evars = List.filter (fun (_, t) -> Term.is_var Term.Eigen t) seq.Sequent.vars in
  if evars = []
  then ()
  else
    Format.fprintf
      ppf
      "Vars: @[<2>%a@]@."
      pr_varlst
      (List.filter Term.is_uninstantiated evars);
  if nvars = [] then () else Format.fprintf ppf "Nominals: @[<2>%a@]@." pr_varlst nvars;
  if Context.CtxVarCtx.is_empty seq.Sequent.ctxvars
  then ()
  else Format.fprintf ppf "Contexts: @[<2>%a@]@." pr_ctxvarlst seq.Sequent.ctxvars;
  Format.fprintf
    ppf
    "@[%a@]@.==================================@."
    pr_hyps
    seq.Sequent.hyps;
  Format.fprintf ppf "%a@.@." pr_formula seq.Sequent.goal
;;

let rec pr_uterm ppf = function
  | Uterms.UConst (_, id) -> pr_str ppf id
  | Uterms.ULam (_, (_, id, None), utm) ->
    Format.fprintf ppf "@[<2>[%a]@,%a@]" pr_str id pr_uterm utm
  | Uterms.ULam (_, (_, id, Some ty), utm) ->
    Format.fprintf ppf "@[<2>[%a@ :@ %a]@,%a@]" pr_str id pr_ty ty pr_uterm utm
  | Uterms.UPi (_, (_, id), uty, utm) ->
    Format.fprintf ppf "@[<2>{%a@,:@,%a}@,%a@]" pr_str id pr_uterm uty pr_uterm utm
  | Uterms.UApp (_, utm1, (Uterms.ULam _ as utm2)) ->
    Format.fprintf ppf "@[<2>%a@ (%a)@]" pr_uterm utm1 pr_uterm utm2
  | Uterms.UApp (_, utm1, utm2) ->
    Format.fprintf ppf "@[<2>%a@ %a@]" pr_uterm utm1 pr_uterm utm2
  | Uterms.UType _ -> pr_str ppf "type"
;;

let rec pr_uctxtm ppf = function
  | Uterms.UNil _ -> ()
  | Uterms.UVar (_, id) -> pr_str ppf id
  | Uterms.UCtxTm (_, Uterms.UNil _, (id, utm)) ->
    Format.fprintf ppf "%a:%a" pr_str id pr_uterm utm
  | Uterms.UCtxTm (_, uctx, (id, utm)) ->
    Format.fprintf ppf "%a,@,%a:%a" pr_uctxtm uctx pr_str id pr_uterm utm
;;

let rec pr_perm ppf = function
  | [] -> ()
  | [ (n, n') ] -> Format.fprintf ppf "@[%a -> %a@]" pr_str n pr_str n'
  | (n, n') :: r -> Format.fprintf ppf "@[%a -> %a,@] %a" pr_str n pr_str n' pr_perm r
;;

let pr_uctx ppf = function
  | Uterms.UNil _ -> ()
  | uctx -> Format.fprintf ppf "%a@ |-@ " pr_uctxtm uctx
;;

let rec pr_uform ppf = function
  | Uterms.UTop -> pr_str ppf "true"
  | Uterms.UBottom -> pr_str ppf "false"
  | Uterms.UImp (l, r) -> Format.fprintf ppf "@[<2>%a@ =>@ %a@]" pr_uform l pr_uform r
  | Uterms.UOr (l, r) -> Format.fprintf ppf "@[<2>%a@ \\/@ %a@]" pr_uform l pr_uform r
  | Uterms.UAnd (l, r) -> Format.fprintf ppf "@[<2>%a@ /\\@ %a@]" pr_uform l pr_uform r
  | Uterms.UAll (locids, f) ->
    Format.fprintf ppf "@[<2>forall %a,@ %a@]" pr_locidtys locids pr_uform f
  | Uterms.UExists (locids, f) ->
    Format.fprintf ppf "@[<2>exists %a,@ %a@]" pr_locidtys locids pr_uform f
  | Uterms.UCtx (locctxs, f) ->
    Format.fprintf ppf "@[<2>ctx %a,@ %a@]" pr_locctxs locctxs pr_uform f
  | Uterms.UAtm (uctx, utm, uty, ann) ->
    Format.fprintf
      ppf
      "@[<2>{@,%a@,%a@ :@ %a}%a"
      pr_uctx
      uctx
      pr_uterm
      utm
      pr_uterm
      uty
      pr_ann
      ann
  | Uterms.UProp utm -> pr_uterm ppf utm

and pr_locctxs ppf = function
  | [] -> ()
  | (_, v, cty) :: locctx ->
    Format.fprintf ppf "@ %a:%a@,%a" pr_str v pr_str cty pr_locctxs locctx

and pr_locidtys ppf = function
  | [] -> ()
  | (_, (id, None)) :: locidtys ->
    Format.fprintf ppf "@ %a@,%a" pr_str id pr_locidtys locidtys
  | (_, (id, Some ty)) :: locidtys ->
    Format.fprintf ppf "@ %a:%a@,%a" pr_str id pr_ty ty pr_locidtys locidtys
;;

let pr_aid ppf = function
  | id, Some ty -> Format.fprintf ppf "@[<2>%a@ :@ %a@]" pr_str id pr_ty ty
  | id, None -> pr_str ppf id
;;

let pr_udef ppf (f1, f2) = Format.fprintf ppf "%a@ :=%a" pr_uform f1 pr_uform f2

let rec pr_udefs ppf = function
  | [] -> ()
  | [ def ] -> pr_udef ppf def
  | def :: defs -> Format.fprintf ppf "%a;\n%a" pr_udef def pr_udefs defs
;;

let rec pr_common ppf = function
  | Uterms.Undo -> pr_str ppf "undo."
  | Uterms.Set settings -> Format.fprintf ppf "@[<4>Set@ %a@.@]" pr_settings settings

and pr_setting ppf = function
  | Uterms.SearchDepth v -> Format.fprintf ppf "search_depth %a" pr_str (string_of_int v)

and pr_settings ppf settings =
  match settings with
  | [] -> ()
  | [ v ] -> Format.fprintf ppf "%a" pr_setting v
  | s :: tl -> Format.fprintf ppf "%a, %a" pr_setting s pr_settings tl
;;

let rec pr_command ppf = function
  | Uterms.Weaken (name, utm, DefaultDepth) ->
    Format.fprintf ppf "@[<4>weaken %a with %a.@]" pr_clearable name pr_uterm utm
  | Uterms.Weaken (name, utm, WithDepth i) ->
    Format.fprintf
      ppf
      "@[<4>weaken %a with %a %a.@]"
      pr_clearable
      name
      pr_uterm
      utm
      pr_str
      (string_of_int i)
  | Uterms.Abort -> pr_str ppf "abort."
  | Uterms.Skip -> pr_str ppf "skip."
  | Uterms.Search DefaultDepth -> pr_str ppf "search."
  | Uterms.Search (WithDepth i) ->
    Format.fprintf ppf "search %a." pr_str (string_of_int i)
  | Uterms.Ind i -> Format.fprintf ppf "induction on %a." pr_str (string_of_int i)
  | Uterms.Apply (name, args, []) ->
    Format.fprintf ppf "@[<4>apply %a %a.@]" pr_clearable name pr_args args
  | Uterms.Apply (name, args, withs) ->
    Format.fprintf
      ppf
      "@[<4>apply %a %a with %a.@]"
      pr_clearable
      name
      pr_args
      args
      pr_withs
      withs
  | Uterms.Case name -> Format.fprintf ppf "cases %a." pr_clearable name
  | Uterms.Exists utm -> Format.fprintf ppf "@[<4>exists %a.@]" pr_uterm utm
  | Uterms.Split -> pr_str ppf "split."
  | Uterms.Left -> pr_str ppf "left."
  | Uterms.Right -> pr_str ppf "right."
  | Uterms.Intros -> pr_str ppf "intros."
  | Uterms.Assert (uform, DefaultDepth) ->
    Format.fprintf ppf "@[<4>assert %a.@]" pr_uform uform
  | Uterms.Assert (uform, WithDepth i) ->
    Format.fprintf ppf "@[<4>assert %a %a.@]" pr_uform uform pr_str (string_of_int i)
  | Uterms.PermuteCtx (name, uctx) ->
    Format.fprintf ppf "@[<4>ctxpermute %a to %a.@]" pr_clearable name pr_uctxtm uctx
  | Uterms.Permute (name, perm) ->
    Format.fprintf ppf "@[<4>permute %a to %a.@]" pr_clearable name pr_perm perm
  | Uterms.Strengthen name -> Format.fprintf ppf "strengthen %a." pr_clearable name
  | Uterms.Inst (name, withs, DefaultDepth) ->
    Format.fprintf ppf "@[<4>inst %a with %a.@]" pr_clearable name pr_withs withs
  | Uterms.Inst (name, withs, WithDepth i) ->
    Format.fprintf
      ppf
      "@[<4>inst %a with %a %a.@]"
      pr_clearable
      name
      pr_withs
      withs
      pr_str
      (string_of_int i)
  | Uterms.Prune id -> Format.fprintf ppf "prune %a." pr_str id
  | Uterms.Unfold (None, []) -> pr_str ppf "unfold."
  | Uterms.Unfold (Some hid, []) -> Format.fprintf ppf "unfold %a." pr_str hid
  | Uterms.Unfold (None, withs) ->
    Format.fprintf ppf "@[<4>unfold with %a.@]" pr_withs withs
  | Uterms.Unfold (Some hid, withs) ->
    Format.fprintf ppf "@[<4>unfold %a with %a.@]" pr_str hid pr_withs withs
  | Uterms.AppDfn (did, None, []) -> Format.fprintf ppf "appdfn %a." pr_str did
  | Uterms.AppDfn (did, Some hid, []) ->
    Format.fprintf ppf "appdfn %a to %a." pr_str did pr_str hid
  | Uterms.AppDfn (did, None, withs) ->
    Format.fprintf ppf "@[<4>appdfn %a with %a.@]" pr_str did pr_withs withs
  | Uterms.AppDfn (did, Some hid, withs) ->
    Format.fprintf
      ppf
      "@[<4>appdfn %a to %a with %a.@]"
      pr_str
      did
      pr_str
      hid
      pr_withs
      withs
  | Uterms.Common c -> pr_common ppf c

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
  | Uterms.Vws (id, utm) -> Format.fprintf ppf "%a@ =@ %a" pr_str id pr_uterm utm
  | Uterms.Cws (id, uctx) -> Format.fprintf ppf "(%a@ =@ %a)" pr_str id pr_uctxtm uctx

and pr_withs ppf = function
  | [] -> ()
  | [ w ] -> pr_with ppf w
  | w :: withs -> Format.fprintf ppf "%a,@ %a" pr_with w pr_withs withs
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
  | Uterms.Theorem (name, uform) ->
    Format.fprintf ppf "@[<4>Theorem@ %a@,:@ %a.@]" pr_str name pr_uform uform
  | Uterms.Schema (name, uschema) ->
    Format.fprintf ppf "@[<4>Schema@ %a@ :=@ %a.@]" pr_str name pr_uschema uschema
  | Uterms.Specification name ->
    Format.fprintf ppf "@[<4>Specification@ %a.@]" pr_str name
  | Uterms.Quit -> pr_str ppf "Quit."
  | Uterms.Define (aid, defs) ->
    Format.fprintf ppf "@[<4>Define@ %a@ by\n%a.@]" pr_aid aid pr_udefs defs
  | Uterms.TopCommon c -> pr_common ppf c
;;

let rec pr_subst ppf = function
  | [] -> ()
  | (id, tm) :: subst ->
    Format.fprintf ppf "%a -> %a\n%a" pr_str id (pr_term []) tm pr_subst subst
;;

(* use general formmatting functions to print to stdout *)
let print_ty = pr_ty Format.std_formatter
let print_term = pr_term [] Format.std_formatter
let print_sequent = pr_sequent Format.std_formatter
let print_uterm = pr_uterm Format.std_formatter

(* use general formatting functions to generate a string *)
let string_of_ty ty =
  pr_ty Format.str_formatter ty;
  Format.flush_str_formatter ()
;;

let string_of_term tm =
  pr_term [] Format.str_formatter tm;
  Format.flush_str_formatter ()
;;

let string_of_sequent s =
  pr_sequent Format.str_formatter s;
  Format.flush_str_formatter ()
;;

let string_of_formula f =
  pr_formula Format.str_formatter f;
  Format.flush_str_formatter ()
;;

let string_of_ctxexpr e =
  pr_ctxexpr Format.str_formatter e;
  Format.flush_str_formatter ()
;;

let string_of_uterm utm =
  pr_uterm Format.str_formatter utm;
  Format.flush_str_formatter ()
;;

let string_of_uform uform =
  pr_uform Format.str_formatter uform;
  Format.flush_str_formatter ()
;;

let string_of_command command =
  pr_command Format.str_formatter command;
  Format.flush_str_formatter ()
;;

let string_of_topcommand topcommand =
  pr_topcommand Format.str_formatter topcommand;
  Format.flush_str_formatter ()
;;

let string_of_subst subst =
  pr_subst Format.str_formatter subst;
  Format.flush_str_formatter ()
;;

let string_of_ctxvarty ctxvarty =
  pr_ctxty Format.str_formatter ctxvarty;
  Format.flush_str_formatter ()
;;
