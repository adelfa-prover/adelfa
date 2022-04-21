open Term
open Extensions
  
(* LF Typing *)
exception NotLFTerm of term
exception NotLFType of term
exception TypeMismatch of term * term

let wf_type sign _ ty =
  match ty with
  | Var v when v.tag = Constant ->
     if Signature.is_type sign v.name
     then ()
     else raise (NotLFType ty) 
  | Type -> ()
  | Pi(_,_) ->
     () (* TODO finish *)
  | _ -> ()
                                   
let wf_ctx sign ctx =
  let rec aux ctx =
    match ctx with
    | [] -> ()
    | ((_,ty)::ctx') ->
       wf_type sign ctx' ty;
       aux ctx'
  in
  aux ctx
                                   
let rec get_type sign (ctx:Term.lftyctx) tm =
  match norm tm with
  | Var v when v.tag = Constant ->
    if Signature.is_obj sign v.name
    then
      let od = Signature.lookup_obj_decl sign v.name in
      od.Signature.typ
    else
      raise (NotLFTerm tm)
  | Var v when v.tag = Nominal ->
    if List.mem_assoc v ctx 
    then
      List.assoc v ctx
    else
      raise (NotLFTerm tm)
  | App(h,_) ->
     let h_ty = get_type sign ctx h in
     h_ty
  | _ -> bugf "Unexpected term when getting type"
and check_type sign (ctx:Term.lftyctx) tm ty =
  match tm with
  | Var _ | App _ ->
    let found_ty = get_type sign ctx tm in
    if eq found_ty ty
    then ty
    else raise (TypeMismatch (ty, found_ty))
  | Lam([],body) -> check_type sign ctx body ty
  | Lam(bndrs,body) ->
     (match ty with
      | Pi(tybndrs, tybody) ->
         (match bndrs, tybndrs with
          | [],[] -> check_type sign ctx body tybody
          | ((tmv,tmty)::tmbndrs'),((tyv,tyty)::tybndrs') ->
             (* substitute a new nominal for both and keep checking under extended context *)
               let (n,_) =
                 Term.fresh_wrt ~ts:4 Nominal "n" tmty (List.map (fun (v,ty) -> (v.name,ty)) ctx)
               in
               let tm' = replace_term_vars [(tmv,n)] (Lam(tmbndrs',body)) in
               let ty' = replace_term_vars [(tyv.name,n)] (Pi(tybndrs',tybody)) in
               check_type sign ((Term.term_to_var n,tyty)::ctx) tm' ty' 
          | _ -> 
            (* couldn't happen when terms are weakly well formed. *)
            assert false)
      | App _ | Var _ ->
        (* couldn't happen when terms are weakly well formed. *)
        assert false
      | _ -> raise (NotLFType ty))
  | _ -> bugf "Unexpected term when checking type"

(* Context Expression Typing *)
(* given a particular context variable context, determines if the 
   given context expression satisfies the given schema. *)
let of_schema nvars ctxvars ctx (id,schema) =
  let ntys = List.map (fun (_,t) -> Term.get_var_ty t) nvars in
  (* if block is instance of one block schema *)
  let is_block block =
    let instance (Context.B(vars,entries)) =
      (* try to end if cannot be a match *)
      if List.length block != List.length entries
      then false
      else  
    (* make fresh logic vars for vars
       substitute into the types in entries
       substitute the nominals from the block into types of entries
       attempt to unify this generalized block instance with the block
       (not actually unification; only want to instantiate in the entries)
    *)
        let var_subst =
          List.map
            (fun (id,ty) ->
             (id,Term.app
                   (Term.fresh (Type.tyarrow ntys ty))
                   (List.map snd nvars)))
            vars
        in
        let nominal_subst =
          List.map2 (fun (n,_) (v,_) -> (n.Term.name, Term.var_to_term v)) entries block
        in
        let gen_block =
          List.init
            (List.length entries)
            (fun i ->
              (fst (List.nth block i),
              Term.replace_term_vars
                        ((List.take (i-1) nominal_subst) @ var_subst)
                        (snd (List.nth entries i))) )
        in
        try
          List.iter2
            (fun (_,gen_ty) (_,block_ty) -> Unify.right_unify gen_ty block_ty)
            gen_block
            block;
          true
        with _ -> false
    in
    List.fold_left (fun tv bsch -> tv || instance bsch) false schema
  in
  let rec aux ctx block=
    match ctx with
    | Context.Nil ->
      if List.length block = 0
      then
        true
      else
        is_block block
    | Context.Ctx(ctx',(n,ty)) ->
      if aux ctx' ((n,ty)::block)
      then true
      else
        is_block block && aux ctx' [n,ty]
    | Context.Var ctx_id ->
       let Context.CtxTy(s,_) = List.assoc ctx_id ctxvars in
       s = id
  in
  aux ctx []


(* Check arity typeing *)
exception TypeError of Type.ty * Type.ty
            
let rec match_tys (l1:Type.ty list) (l2:Type.ty list) =
  match l1,l2 with
  | (h1::l1'), (h2::l2') ->
     if Type.eq h1 h2
     then match_tys l1' l2'
     else
        raise (TypeError(h1,h2))
  | _ -> ()
                
let apply_ty fty argtys =
  match fty, argtys with
  | _,[] -> fty
  | (Type.Ty(atys,base)),_ ->
     let argtys_len = List.length argtys in
     let atys_len = List.length atys in
     match_tys atys argtys;
     if argtys_len <= atys_len
     then Type.tyarrow (List.drop argtys_len atys) (Type.tybase base)
     else
        raise (TypeError(Type.tyarrow atys Type.oty,Type.tyarrow argtys Type.oty))
                              
let rec infer_ty env tm  =
  match observe (norm tm) with
  | Var(v) -> v.ty
  | Lam(vs,body) ->
    let _,typs = List.split vs in
    Type.tyarrow
      typs
      (infer_ty ((List.rev typs) @ env) body)
  | App(h,args) ->
     let fty = infer_ty env h in
     let argtys = List.map (infer_ty env) args in
     apply_ty fty argtys
  | DB i -> List.nth env (i-1)
  | _ -> assert false

let of_type tm ty =
  let got_type = infer_ty [] tm in
  if
    Type.eq got_type ty
  then
    true
  else
    raise @@ TypeError (ty, got_type)
