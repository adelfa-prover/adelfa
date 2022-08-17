open Uterms
open Extensions

type typing_error =
  | NoType of pos * Term.id
  | TypeMismatch of pos * Type.ty * Type.ty
  | TooManyArgs of pos
  | BadSchema of pos * string
  | BadDefinition of pos * Term.id
  | BadProp of pos
  | UnknownContext of pos * Context.ctx_var
  | UnknownConstant of pos * Term.id
  | Other of pos * string

exception TypingError of typing_error

let notype pos id = NoType (pos, id)
let typemismatch pos expected got = TypeMismatch (pos, expected, got)
let badschema pos id = BadSchema (pos, id)
let baddefinition pos id = BadDefinition (pos, id)
let badprop pos = BadProp pos
let unknowncontext pos id = UnknownContext (pos, id)
let unknownconstant pos id = UnknownConstant (pos, id)
let toomanyargs pos = TooManyArgs pos
let other pos s = Other (pos, s)

let get_error_pos = function
  | NoType (pos, _)
  | TypeMismatch (pos, _, _)
  | BadSchema (pos, _)
  | BadDefinition (pos, _)
  | BadProp pos
  | UnknownContext (pos, _)
  | UnknownConstant (pos, _)
  | TooManyArgs pos
  | Other (pos, _) -> pos
;;

let explain_error = function
  | NoType (_, id) -> "could not determine type for variable " ^ id
  | TypeMismatch (_, expected, got) ->
    "expected type\n  "
    ^ Print.string_of_ty expected
    ^ "\nbut got type\n  "
    ^ Print.string_of_ty got
  | TooManyArgs _ -> "term applied to too many arguments."
  | BadSchema (_, id) -> "can't find context schema " ^ id
  | BadDefinition (_, id) -> "No definition for " ^ id
  | BadProp _ -> "Expected a defined expression."
  | UnknownContext (_, id) -> "unknown context variable " ^ id
  | UnknownConstant (_, id) -> "unknown constant " ^ id
  | Other (_, s) -> s
;;

let nominal_regexp = Str.regexp "['n']['0-9']*"
let maybe_nominal name = Str.string_match nominal_regexp name 0

let trans_term lf_sig evar_ctx logicvar_ctx nvar_ctx bvar_ctx ty_opt tm =
  let rec trans_match nvar_ctx bvar_ctx ty = function
    (* order for resolving of names: 
             1. bound variables
             2. existing nominal constants
             3. logic variables
             4. eigen variable
             5. constants from sig
             6. new nominal constant (only if name is `n' followed by a number *)
    | UConst (pos, id) when List.mem_assoc id bvar_ctx ->
      let got = List.assoc id bvar_ctx in
      if Option.is_some !got
      then (
        let got_ty = Term.get_var_ty (Option.get !got) in
        if Type.eq ty got_ty
        then Option.get !got, nvar_ctx
        else raise (TypingError (typemismatch pos ty got_ty)))
      else (
        let t = Term.const ~ts:2 id ty in
        got := Some t;
        t, nvar_ctx)
    | UConst (pos, id) when List.mem_assoc id nvar_ctx ->
      let got = List.assoc id nvar_ctx in
      if Option.is_some !got
      then (
        let got_ty = Term.get_var_ty (Option.get !got) in
        if Type.eq ty got_ty
        then Option.get !got, nvar_ctx
        else raise (TypingError (typemismatch pos ty got_ty)))
      else (
        let t = Term.nominal_var id ty in
        got := Some t;
        t, nvar_ctx)
    | UConst (pos, id) when List.mem_assoc id logicvar_ctx ->
      let got = List.assoc id logicvar_ctx in
      if Option.is_some !got
      then (
        let got_ty = Term.get_var_ty (Option.get !got) in
        if Type.eq ty got_ty
        then Option.get !got, nvar_ctx
        else raise (TypingError (typemismatch pos ty got_ty)))
      else (
        let t = Term.var Term.Logic id 1 ty in
        got := Some t;
        t, nvar_ctx)
    | UConst (pos, id) when List.mem_assoc id evar_ctx ->
      let got = List.assoc id evar_ctx in
      if Option.is_some !got
      then (
        let got_ty = Term.get_var_ty (Option.get !got) in
        if Type.eq ty got_ty
        then Option.get !got, nvar_ctx
        else raise (TypingError (typemismatch pos ty got_ty)))
      else (
        let t = Term.var Term.Eigen id 1 ty in
        got := Some t;
        t, nvar_ctx)
    | UConst (pos, id) ->
      if Signature.is_obj lf_sig id
      then (
        let got = Term.erase (Signature.lookup_obj_decl lf_sig id).Signature.typ in
        if Type.eq ty got
        then Term.const id ty, nvar_ctx
        else raise (TypingError (typemismatch pos ty got)))
      else if Signature.is_type lf_sig id
      then (
        let got = Term.erase (Signature.lookup_type_decl lf_sig id).Signature.kind in
        if Type.eq ty got
        then Term.const id ty, nvar_ctx
        else raise (TypingError (typemismatch pos ty got)))
      else if maybe_nominal id
      then (
        let t = Term.nominal_var id ty in
        t, List.append nvar_ctx [ id, ref (Some t) ])
      else raise (TypingError (unknownconstant pos id))
    | ULam (pos, (idpos, id, tyopt), tm) ->
      (match ty with
       | Type.Ty (argty :: args, bty) ->
         if Option.is_some tyopt && not (Type.eq argty (Option.get tyopt))
         then raise (TypingError (typemismatch pos (Option.get tyopt) argty));
         let tm', nvar_ctx' =
           trans_match
             nvar_ctx
             ((id, ref (Some (Term.const ~ts:2 id argty))) :: bvar_ctx)
             (Type.Ty (args, bty))
             tm
         in
         Term.abstract id argty tm', nvar_ctx'
       | _ when Option.is_none tyopt -> raise (TypingError (notype idpos id))
       | _ ->
         raise (TypingError (typemismatch pos (Type.tyarrow [ Option.get tyopt ] ty) ty)))
    | UPi (pos, (_, id), typ, tm) ->
      (match ty with
       | Type.Ty ([], "o") ->
         let ty', nvar_ctx' = trans_match nvar_ctx bvar_ctx Type.oty typ in
         let aty = Term.erase ty' in
         let tm', nvar_ctx'' =
           trans_match
             nvar_ctx'
             ((id, ref (Some (Term.const ~ts:2 id aty))) :: bvar_ctx)
             Type.oty
             tm
         in
         Term.pi [ Term.term_to_var (Term.const ~ts:2 id aty), ty' ] tm', nvar_ctx''
       | _ -> raise (TypingError (typemismatch pos Type.oty ty)))
    | UApp (pos, tm1, tm2) ->
      let tm1', Type.Ty (args, bty), nvar_ctx' = trans_get nvar_ctx bvar_ctx tm1 in
      (match args with
       | argty :: args' ->
         let tm2', nvar_ctx'' = trans_match nvar_ctx' bvar_ctx argty tm2 in
         if Type.eq ty (Type.Ty (args', bty))
         then Term.app tm1' [ tm2' ], nvar_ctx''
         else raise (TypingError (typemismatch pos ty (Type.Ty (args', bty))))
       | [] -> raise (TypingError (toomanyargs pos)))
    | UType _ -> Term.Type, nvar_ctx
  and trans_get nvar_ctx bvar_ctx = function
    | UConst (pos, id) when List.mem_assoc id bvar_ctx ->
      let got = List.assoc id bvar_ctx in
      if Option.is_some !got
      then (
        let ty = Term.get_var_ty (Option.get !got) in
        Option.get !got, ty, nvar_ctx)
      else raise (TypingError (notype pos id))
    | UConst (pos, id) when List.mem_assoc id nvar_ctx ->
      let got = List.assoc id nvar_ctx in
      if Option.is_some !got
      then (
        let ty = Term.get_var_ty (Option.get !got) in
        Option.get !got, ty, nvar_ctx)
      else raise (TypingError (notype pos id))
    | UConst (pos, id) when List.mem_assoc id logicvar_ctx ->
      let got = List.assoc id logicvar_ctx in
      if Option.is_some !got
      then (
        let ty = Term.get_var_ty (Option.get !got) in
        Option.get !got, ty, nvar_ctx)
      else raise (TypingError (notype pos id))
    | UConst (pos, id) when List.mem_assoc id evar_ctx ->
      let got = List.assoc id evar_ctx in
      if Option.is_some !got
      then (
        let ty = Term.get_var_ty (Option.get !got) in
        Option.get !got, ty, nvar_ctx)
      else raise (TypingError (notype pos id))
    | UConst (pos, id) ->
      if Signature.is_obj lf_sig id
      then (
        let ty = Term.erase (Signature.lookup_obj_decl lf_sig id).typ in
        Term.const id ty, ty, nvar_ctx)
      else if Signature.is_type lf_sig id
      then (
        let ty = Term.erase (Signature.lookup_type_decl lf_sig id).kind in
        Term.const id ty, ty, nvar_ctx)
      else raise (TypingError (unknownconstant pos id))
    | ULam (_, (idpos, id, tyopt), tm) ->
      let bvar = id, ref (Some (Term.const ~ts:2 id (Option.get tyopt))) in
      let tm', ty, nvar_ctx' = trans_get nvar_ctx (bvar :: bvar_ctx) tm in
      let id_ty_opt = !(snd bvar) in
      if Option.is_some id_ty_opt
      then (
        let argty = Term.get_var_ty (Option.get id_ty_opt) in
        Term.abstract id argty tm', Type.tyarrow [ argty ] ty, nvar_ctx')
      else raise (TypingError (notype idpos id))
    | UPi (_, (_, id), typ, tm) ->
      let typ', nvar_ctx' = trans_match nvar_ctx bvar_ctx Type.oty typ in
      let atyp = Term.erase typ' in
      let tm', nvar_ctx'' =
        trans_match
          nvar_ctx'
          ((id, ref (Some (Term.const ~ts:2 id atyp))) :: bvar_ctx)
          Type.oty
          tm
      in
      ( Term.pi [ Term.term_to_var (Term.const ~ts:2 id atyp), typ' ] tm'
      , Type.oty
      , nvar_ctx'' )
    | UApp (pos, tm1, tm2) ->
      let tm1', arrty, nvar_ctx' = trans_get nvar_ctx bvar_ctx tm1 in
      (match arrty with
       | Type.Ty (argty :: args, bty) ->
         let tm2', nvar_ctx'' = trans_match nvar_ctx' bvar_ctx argty tm2 in
         Term.app tm1' [ tm2' ], Type.Ty (args, bty), nvar_ctx''
       | _ -> raise (TypingError (toomanyargs pos)))
    | UType _ -> Term.Type, Type.oty, nvar_ctx
  in
  match ty_opt with
  | Some ty -> trans_match nvar_ctx bvar_ctx ty tm
  | None ->
    let tm', _, nvar_ctx' = trans_get nvar_ctx bvar_ctx tm in
    tm', nvar_ctx'
;;

let rec trans_ctx lf_sig evar_ctx logicvar_ctx ctxvar_ctx nvar_ctx = function
  | UNil _ -> Context.Nil, nvar_ctx
  | UVar (pos, name) ->
    if Sequent.ctxvar_mem ctxvar_ctx name
    then Context.Var (Context.ctx_var name), nvar_ctx
    else raise (TypingError (unknowncontext pos name))
  | UCtxTm (_, uctx, (name, utm)) ->
    let ctx, nvar_ctx' =
      trans_ctx lf_sig evar_ctx logicvar_ctx ctxvar_ctx nvar_ctx uctx
    in
    let ctx_entries = Context.ctxexpr_to_ctx (Sequent.get_cvar_tys ctxvar_ctx) ctx in
    let tm, nvar_ctx'' =
      trans_term
        lf_sig
        evar_ctx
        logicvar_ctx
        (List.append
           (List.rev
              (List.map
                 (fun (x, _) -> x.Term.name, ref (Some (Term.var_to_term x)))
                 ctx_entries))
           nvar_ctx')
        []
        (Some Type.oty)
        utm
    in
    (try
       ( Context.Ctx (ctx, (Term.term_to_var (Term.nominal_var name (Term.erase tm)), tm))
       , nvar_ctx'' )
     with
     | Assert_failure _ ->
       raise (TypingError (unknownconstant (Uterms.get_pos utm) (Term.get_ty_head tm))))
;;

let trans_formula lf_sig schemas dfns evar_ctx logicvar_ctx ctxvar_ctx nvar_ctx formula =
  let rec trans logicvar_ctx (ctxvar_ctx : Sequent.cvar_entry list) nvar_ctx = function
    | UTop -> Formula.Top, nvar_ctx
    | UBottom -> Formula.Bottom, nvar_ctx
    | UImp (f1, f2) ->
      let f1', nvar_ctx = trans logicvar_ctx ctxvar_ctx [] f1 in
      let f2', nvar_ctx' = trans logicvar_ctx ctxvar_ctx nvar_ctx f2 in
      Formula.imp f1' f2', nvar_ctx'
    | UOr (f1, f2) ->
      let f1', nvar_ctx = trans logicvar_ctx ctxvar_ctx [] f1 in
      let f2', nvar_ctx' = trans logicvar_ctx ctxvar_ctx nvar_ctx f2 in
      Formula.f_or f1' f2', nvar_ctx'
    | UAnd (f1, f2) ->
      let f1', nvar_ctx = trans logicvar_ctx ctxvar_ctx [] f1 in
      let f2', nvar_ctx' = trans logicvar_ctx ctxvar_ctx nvar_ctx f2 in
      Formula.f_and f1' f2', nvar_ctx'
    | UAll (locids, f) ->
      let _, idtys = List.split locids in
      let new_logicvar_ctx =
        List.map
          (fun (x, y) ->
            ( x
            , if Option.is_some y
              then ref (Some (Term.var Term.Logic x 1 (Option.get y)))
              else ref None ))
          idtys
      in
      let f', nvar_ctx' =
        trans (List.append (List.rev new_logicvar_ctx) logicvar_ctx) ctxvar_ctx nvar_ctx f
      in
      if List.for_all (fun (_, x) -> Option.is_some !x) new_logicvar_ctx
      then (
        let tyctx =
          List.map (fun (x, y) -> x, Term.get_var_ty (Option.get !y)) new_logicvar_ctx
        in
        Formula.forall tyctx f', nvar_ctx')
      else (
        let untyped, _ = List.find (fun (_, x) -> Option.is_none !x) new_logicvar_ctx in
        let pos, _ = List.find (fun (_, (x, _)) -> x = untyped) locids in
        raise (TypingError (notype pos untyped)))
    | UExists (locids, f) ->
      let _, idtys = List.split locids in
      let new_logicvar_ctx =
        List.map
          (fun (x, y) ->
            ( x
            , if Option.is_some y
              then ref (Some (Term.var Term.Logic x 1 (Option.get y)))
              else ref None ))
          idtys
      in
      let f', nvar_ctx' =
        trans (List.append (List.rev new_logicvar_ctx) logicvar_ctx) ctxvar_ctx nvar_ctx f
      in
      if List.for_all (fun (_, x) -> Option.is_some !x) new_logicvar_ctx
      then (
        let tyctx =
          List.map (fun (x, y) -> x, Term.get_var_ty (Option.get !y)) new_logicvar_ctx
        in
        Formula.exists tyctx f', nvar_ctx')
      else (
        let untyped, _ = List.find (fun (_, x) -> Option.is_none !x) new_logicvar_ctx in
        let pos, _ = List.find (fun (_, (x, _)) -> x = untyped) locids in
        raise (TypingError (notype pos untyped)))
    | UCtx (loccids, f) ->
      let cids = List.map (fun (_, x, y) -> x, y) loccids in
      let process_locid (pos, id, schema) =
        let cvar = Context.ctx_var id in
        try
          let _ = Hashtbl.find schemas schema in
          cvar, ref [], Context.ctx_typ ~id:schema ()
        with
        | Not_found -> raise (TypingError (badschema pos schema))
      in
      let ctxids = List.map process_locid loccids in
      let f', nvar_ctx' =
        trans logicvar_ctx (List.append (List.rev ctxids) ctxvar_ctx) nvar_ctx f
      in
      Formula.ctx cids f', nvar_ctx'
    | UAtm (uctx, utm, uty, ann) ->
      let ctx, nvar_ctx' =
        trans_ctx lf_sig evar_ctx logicvar_ctx ctxvar_ctx nvar_ctx uctx
      in
      let nvar_ctx'' =
        List.append
          (List.rev
             (List.map
                (fun (x, _) -> x.Term.name, ref (Some (Term.var_to_term x)))
                (Context.ctxexpr_to_ctx (Sequent.get_cvar_tys ctxvar_ctx) ctx)))
          nvar_ctx'
      in
      let a, nvar_ctx''' =
        trans_term lf_sig evar_ctx logicvar_ctx nvar_ctx'' [] (Some Type.oty) uty
      in
      let arity_typ =
        try Term.erase a with
        | Assert_failure _ ->
          raise (TypingError (unknownconstant (Uterms.get_pos uty) (Term.get_ty_head a)))
      in
      let m, nvar_ctx'''' =
        trans_term lf_sig evar_ctx logicvar_ctx nvar_ctx''' [] (Some arity_typ) utm
      in
      Formula.atm ~ann ctx m a, nvar_ctx''''
    | UProp utm ->
      let prop, uargs =
        try Uterms.get_hid_and_args utm with
        | Failure _ -> raise (TypingError (badprop (Uterms.get_pos utm)))
      in
      let argtys =
        try
          match List.assoc prop dfns with
          | Type.Ty (argtys, "prop") -> argtys
          | _ -> bugf "Expected a prop type"
        with
        | Not_found -> raise (TypingError (baddefinition (Uterms.get_pos utm) prop))
        | Failure _ -> raise (TypingError (badprop (Uterms.get_pos utm)))
      in
      let args', nvar_ctx' =
        try
          List.fold_right2
            (fun tm ty (args, nvars) ->
              let tm, nvars' =
                trans_term lf_sig evar_ctx logicvar_ctx nvars [] (Some ty) tm
              in
              tm :: args, nvars')
            uargs
            argtys
            ([], nvar_ctx)
        with
        | Invalid_argument _ ->
          let num_uargs, num_tys = List.length uargs, List.length argtys in
          if num_uargs < num_tys
          then
            raise
              (TypingError
                 (typemismatch
                    (Uterms.get_pos utm)
                    Type.propty
                    (Type.tyarrow
                       (List.take_last (num_tys - num_uargs) argtys)
                       Type.propty)))
          else
            (* num_tys < num_uargs *)
            raise (TypingError (toomanyargs (Uterms.get_pos utm)))
      in
      Formula.Prop (prop, args'), nvar_ctx'
  in
  fst (trans logicvar_ctx ctxvar_ctx nvar_ctx formula)
;;

let trans_schema lf_sig ublock_schemas =
  (* Given an untyped block schema, perform arity type inference
     to transform into a valid block schema *)
  let trans_blockschema (locids, ublock_entries) =
    let logicvar_ctx = List.map (fun (_, id) -> id, ref None) locids in
    let entry_list =
      List.fold_left
        (fun prev_entries (_, id, utm) ->
          let tm, nvar_ctx =
            trans_term
              lf_sig
              []
              logicvar_ctx
              []
              (List.map
                 (fun (v, _) -> v.Term.name, ref (Some (Term.var_to_term v)))
                 prev_entries)
              (Some Type.oty)
              utm
          in
          match nvar_ctx with
          | [] -> (Term.term_to_var (Term.const id (Term.erase tm)), tm) :: prev_entries
          | (id, _) :: _ ->
            raise (TypingError (unknownconstant (Lexing.dummy_pos, Lexing.dummy_pos) id)))
        []
        ublock_entries
    in
    match List.filter (fun (_, x) -> Option.is_none !x) logicvar_ctx with
    | [] ->
      Context.B
        ( List.map (fun (x, y) -> x, Term.get_var_ty (Option.get !y)) logicvar_ctx
        , List.rev entry_list )
    | (n, _) :: _ ->
      let pos, id = List.find (fun (_, x) -> x = n) locids in
      raise (TypingError (notype pos id))
  in
  List.map trans_blockschema ublock_schemas
;;

let trans_dfn
  (lf_sig : Signature.signature)
  (schemas : (string, Context.ctx_schema) Hashtbl.t)
  (dfns : (string * Type.ty) list)
  (name : Term.id)
  (ty : Type.ty)
  (udefs : Uterms.udef list)
  =
  let trans_def (ufleft, ufright) =
    match ufleft with
    | Uterms.UProp _ ->
      (* find unbound names across both formulas.
          create new, untyped logic variables for these names.
          attempt to translate both formulas with the extended logic variable context.
          if at end any of the new variables is untyped, raise error.
          otherwise, save context as the implicit prefix. *)
      let dfns' = (name, ty) :: dfns in
      let new_var_lst =
        Uterms.extract_unbound_uform [] ufleft @ Uterms.extract_unbound_uform [] ufright
        |> List.unique
        |> List.remove_all (fun id ->
             List.mem_assoc id dfns'
             || Signature.is_obj lf_sig id
             || Signature.is_type lf_sig id)
      in
      let new_nominal_ctx, new_logicvar_ctx =
        let regexp = Str.regexp "n[']*[0-9]*" in
        List.partition (fun id -> Str.string_match regexp id 0) new_var_lst
        |> fun (l1, l2) ->
        List.map (fun x -> x, ref None) l1, List.map (fun x -> x, ref None) l2
      in
      let fleft =
        trans_formula lf_sig schemas dfns' [] new_logicvar_ctx [] new_nominal_ctx ufleft
      in
      let fright =
        trans_formula lf_sig schemas dfns' [] new_logicvar_ctx [] new_nominal_ctx ufright
      in
      if List.for_all (fun (_, x) -> Option.is_some !x) new_logicvar_ctx
      then
        if List.for_all (fun (_, x) -> Option.is_some !x) new_nominal_ctx
        then (
          let support =
            List.map (fun (x, y) -> x, Term.get_var_ty (Option.get !y)) new_nominal_ctx
          in
          let tyctx =
            List.map (fun (x, y) -> x, Term.get_var_ty (Option.get !y)) new_logicvar_ctx
          in
          support, tyctx, fleft, fright)
        else (
          let untyped, _ = List.find (fun (_, x) -> Option.is_none !x) new_nominal_ctx in
          raise (TypingError (notype (Lexing.dummy_pos, Lexing.dummy_pos) untyped)))
      else (
        let untyped, _ = List.find (fun (_, x) -> Option.is_none !x) new_logicvar_ctx in
        raise (TypingError (notype (Lexing.dummy_pos, Lexing.dummy_pos) untyped)))
    | _ -> raise (TypingError (badprop (Lexing.dummy_pos, Lexing.dummy_pos)))
  in
  let defs = List.map trans_def udefs in
  name, (ty, defs)
;;
