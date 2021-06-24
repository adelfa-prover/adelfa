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

let get_const_id (UConst(_,id)) = id
             
let get_pos = function
  | UConst(p,_)
  | ULam(p,_,_)
  | UPi(p,_,_,_)
  | UApp(p,_,_) -> p
  | UType(p) -> p

let change_pos p = function
  | UConst(_,s) -> UConst(p,s)
  | ULam(_,s,tm) -> ULam(p,s,tm)
  | UPi(_,s,ty,b) -> UPi(p,s,ty,b)
  | UApp(_,t1,t2) -> UApp(p,t1,t2)
  | UType(_) -> UType(p)

let get_hid_and_args utm =
  let rec aux args = function
    | UConst(pos,id) -> (id, args)
    | UApp(pos, t1, t2) ->
       aux (t2 :: args) t1
  in
  aux [] utm
                     
type uctx =
| UNil of pos
| UVar of pos *id
| UCtxTm of pos * uctx * (id * uterm)
    
type aid = id * (Type.ty option)
    
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

let is_cws = function
  | Cws _ -> true
  | _ -> false

let is_vws = function
  | Vws _ -> true
  | _ -> false

let unwrap_cws (Cws(id,ctx)) = (id, ctx)
let unwrap_vws (Vws(id,tm)) = (id, tm) 
    
type command =
| Skip
| Undo
| Search
| Ind of int
| Apply of clearable * clearable list * uwith list
| Case of clearable
| Exists of uterm
| Split
| Left 
| Right
| Intros 
| Assert of uformula
| Abort
| Weaken of clearable * uterm
| PermuteCtx of clearable * uctx
| Strengthen of clearable
| Inst of clearable * uwith list
| Prune of id
| Unfold of id option * uwith list
| AppDfn of id * (id option) * uwith list

type top_command =
| Theorem of id * uformula
| Schema of id * uschema
| Specification of string
| Quit
| Define of aid * (udef list)


type mode =
| Plus
| Star
| Minus

type placeholder = int
    
type mform =
| True
| Exists of (id * uterm option) list * mform
| Forall of (id * uterm option) list * mform
| ForallI of (id * uterm option) list * mform
| ForallG of placeholder

type callpat = id * ((id option) list)

type order = placeholder
               
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
    | UConst(pos,id) ->
       if List.mem id bvars
       then []
       else [id]
    | ULam (_, (_, id, _), utm) ->
       aux (id ::bvars) utm
    | UPi (_, (_, id), utma, utmm) ->
       (aux bvars utma) @ (aux (id::bvars) utmm)
    | UApp (_, utml, utmr) ->
       (aux bvars utml) @ (aux bvars utmr)
    | UType _ -> []
  in
  List.unique (aux bvars utm)

let extract_unbound_uctx bvars uctx =
  let rec aux = function
  | UNil _ 
  | UVar _ -> []
  | UCtxTm (_, uctx,  (_, utm)) ->
     (aux uctx) @ (extract_unbound_uterm bvars utm)
  in
  List.unique (aux uctx)
                 
let extract_unbound_uform bvars uform =
  let rec aux bvars = function
    | UTop
    | UBottom -> []
    | UImp (ufl, ufr)
    | UOr  (ufl, ufr)
    | UAnd (ufl, ufr) ->
       (aux bvars ufl) @ (aux bvars ufr)
    | UAll (bndrs, uf)
    | UExists (bndrs, uf) ->
       aux (List.map (fun (_,(id,_)) -> id) bndrs @ bvars) uf
    | UCtx (_, uf) ->
       aux bvars uf
    | UAtm (uctx, utmm, utma, _) ->
       (extract_unbound_uctx bvars uctx) @ (extract_unbound_uterm bvars utmm) @ (extract_unbound_uterm bvars utma)
    | UProp (utm) ->
        extract_unbound_uterm bvars utm
  in
  List.unique (aux bvars uform)
