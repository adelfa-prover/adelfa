open OUnit
open Core
open Term

let raises f =
  try
    f ();
    None
  with
    e -> Some e
                    
let assert_string_equal =
  assert_equal ~printer:(fun s -> s)
  
let renumber_term t =
  let rec spin dep t =
    match Term.observe (Term.hnorm t) with
    | Term.Var _ | Term.DB _ | Term.Type -> t
    | Term.Lam (tycx, t) ->
      let (dep, tycx) = List.fold_left begin
        fun (dep, tycx) (v, ty) ->
          let xv = "x" ^ string_of_int dep in
          let dep = dep + 1 in
          let tycx = (xv, ty) :: tycx in
          (dep, tycx)
      end (dep, []) tycx in
      let tycx = List.rev tycx in
      let t = spin dep t in
      Term.lambda tycx t
   | Term.Pi (tycx, t) ->
        let (dep, tycx) = List.fold_left begin
          fun (dep, tycx) (v, ty) ->
            let xv = Term.term_to_var (Term.var Term.Constant ( ("x" ^ string_of_int dep)) 3 (Term.erase ty)) in
            let dep = dep + 1 in
            let tycx = (xv, ty) :: tycx in
            (dep, tycx)
        end (dep, []) tycx in
        let tycx = List.rev tycx in
        let t = spin dep t in
        Term.pi tycx t
    | Term.App (f, ts) ->
        let f = spin dep f in
        let ts = List.map (spin dep) ts in
        Term.app f ts
    | Term.Susp _ | Term.Ptr _ -> assert false
  in
  spin 1 t

let assert_pprint_equal s t =
  let t = Formula.map_terms renumber_term t in
  assert_string_equal s (Print.string_of_formula t)

let assert_formula_equal s t =
  let s = Formula.map_terms renumber_term s in
  let t = Formula.map_terms renumber_term t in
  assert_string_equal (Print.string_of_formula s) (Print.string_of_formula t)

let assert_term_pprint_equal s t =
  let t = renumber_term t in
  assert_string_equal s (Print.string_of_term t)
    
let assert_ty_pprint_equal s t =
  assert_string_equal s (Print.string_of_ty t)
    
let assert_term_equal =
  assert_equal ~cmp:Term.eq ~printer:Print.string_of_term

let assert_ty_equal =
  assert_equal ~printer:Print.string_of_ty

let assert_int_equal =
  assert_equal ~printer:string_of_int
    
let assert_string_list_equal lst1 lst2 =
  assert_int_equal (List.length lst1) (List.length lst2) ;
  ignore (List.map2 assert_string_equal lst1 lst2)
    
let assert_raises_any ?msg (f: unit -> 'a) =
  let str = "expected exception, but no exception was raised." in
    match raises f, msg with
      | Some e, _ -> ()
	  | None, None -> assert_failure str
	  | None, Some s -> assert_failure (Format.sprintf "%s\n%s" s str)

let rec extract_tests path test =
  match path, test with
    | [], _ -> test
    | n::rest, TestList l ->
        TestLabel(string_of_int n, extract_tests rest (List.nth l n))
    | _, TestLabel(name, t) ->
        TestLabel(name, extract_tests path t)
    | _ -> assert false



(* Quick types *)

let isymb = "i"
let ity = Type.oty
let lfity = Term.var Constant isymb 0 ity
let iity = Type.tyarrow [ity] ity
let lfiity = Term.Pi([({Term.tag=Term.Constant ; Term.name="X"; Term.ts=2; Term.ty=ity}, lfity)], lfity)
let iiity = Type.tyarrow [ity; ity] ity
let lfiiity = Term.pi ([({Term.tag=Constant; Term.name="x"; Term.ts=2; Term.ty=ity}, lfity);
                       ({Term.tag=Constant; Term.name="y"; Term.ts=2; Term.ty=ity}, lfity)]) lfity
let iiiity = Type.tyarrow [ity; ity; ity] ity
let lfiiiity = Term.pi ([({Term.tag=Constant; Term.name="x"; Term.ts=2; Term.ty=ity}, lfity);
                        ({Term.tag=Constant; Term.name="y"; Term.ts=2; Term.ty=ity}, lfity);
                        ({Term.tag=Constant; Term.name="z"; Term.ts=2; Term.ty=ity}, lfity)]) lfity

let asymb =  "a"
let aty = Type.oty
let lfaty = Term.var Constant asymb 0 aty
let bsymb =  "b"
let bty = Type.oty
let lfbty = Term.var Constant bsymb 0 bty
let csymb =  "c"
let cty = Type.oty
let lfcty = Term.var Constant csymb 0 cty
let dsymb =  "d"
let dty = Type.oty
let lfdty = Term.var Constant dsymb 0 dty
let esymb =  "e"
let ety = Type.oty
let lfety = Term.var Constant esymb 0 ety

(* Quick term construction *)
let ityvar = Term.var Constant "x" 2 ity
let atyvar = Term.var Constant "a" 2 aty
let btyvar = Term.var Constant "b" 2 bty
let ctyvar = Term.var Constant "c" 2 cty

(* eval sample *)
let tm = const "tm" ity
let app = const "app" iiity
let abs = const "abs" (Type.tyarrow [iity] ity)
let ty = const "ty" ity
let arrow = const "arrow" iiity
let typeof = const "typeof" iiity
let eval = const "eval" iiity
let typeof_app = const "typeof_app" (Type.tyarrow [ity;ity;ity;ity;ity;ity] ity)
let typeof_abs = const "typeof_abs" (Type.tyarrow [iity;ity;ity;iiity] ity)
let eval_app = const "eval_app" (Type.tyarrow [ity;ity;ity;iity;ity;ity] ity)
let eval_abs = const "eval_abs" (Type.tyarrow [iity] ity)

let tm_decl =
  Signature.ty_dec "tm" Term.Type 0 (Signature.Prefix 0) []
let ty_decl =
  Signature.ty_dec "ty" Term.Type 0 (Signature.Prefix 0) []
let typeof_decl =
  Signature.ty_dec
    "typeof"
    (Term.pi
       [(term_to_var (const ~ts:2 "m" ity),tm);
        (term_to_var (const ~ts:2 "a" ity),ty)]
       Term.Type)
    0
    (Signature.Prefix 0)
    []
let eval_decl =
  Signature.ty_dec
    "eval"
    (Term.pi
       [(term_to_var (const ~ts:2 "e" ity),tm);
        (term_to_var (const ~ts:2 "v" ity),tm)]
       Term.Type)
    0
    (Signature.Prefix 0)
    []
    
let arrow_decl =
  Signature.obj_dec
    "arrow"
    (Term.pi
       [(term_to_var (const ~ts:2 "t1" ity),ty);
        (term_to_var (const ~ts:2 "t2" ity),ty)]
       ty)
    0
    (Signature.Prefix 0)
let app_decl =
  Signature.obj_dec
    "app"
    (Term.pi
       [(term_to_var (const ~ts:2 "m" ity),tm);
        (term_to_var (const ~ts:2 "n" ity),tm)]
       tm)
    0
    (Signature.Prefix 0)
let abs_decl =
  Signature.obj_dec
    "abs"
    (Term.pi
       [(term_to_var (const ~ts:2 "r" iity),
         Term.pi [(term_to_var (const ~ts:2 "x" ity),tm)] tm)]
       tm)
    0
    (Signature.Prefix 0)
let typeof_app_decl =
  let m = const ~ts:2 "M" ity in
  let n = const ~ts:2 "N" ity in
  let t1 = const ~ts:2 "T1" ity in
  let t2 = const ~ts:2 "T2" ity in
  Signature.obj_dec
    "typeof_app"
    (Term.pi
       [(term_to_var m, tm);
        (term_to_var n, tm);
        (term_to_var t1, ty);
        (term_to_var t2, ty);
        (term_to_var (const ~ts:2 "a1" ity), Term.app typeof [m;Term.app arrow [t2;t1]]);
        (term_to_var (const ~ts:2 "a2" ity), Term.app typeof [n;t2])]
       (Term.app typeof [Term.app app [m;n]; t1]))
    0
    (Signature.Prefix 0)
let typeof_abs_decl =
  let r = const ~ts:2 "R" iity in
  let t1 = const ~ts:2 "T1" ity in
  let t2 = const ~ts:2 "T2" ity in
  let x = const ~ts:2 "x" ity in
  let z = const ~ts:2 "z" ity in
  Signature.obj_dec
    "typeof_abs"
    (Term.pi
       [(term_to_var r, Term.pi [(term_to_var (const ~ts:2 "x" ity),tm)] tm);
        (term_to_var t1, ty);
        (term_to_var t2, ty);
        (term_to_var (const ~ts:2 "a" iiity),
         Term.pi
           [(term_to_var x, tm);
            (term_to_var (const ~ts:2 "y" ity),Term.app typeof [x;t1])]
           (Term.app typeof [Term.app r [x];t2]))]
       (Term.app typeof [Term.app abs [(Term.abstract "z" ity (Term.app r [z]))]; Term.app arrow [t1;t2]]))
    0
    (Signature.Prefix 0)
let eval_app_decl =
  let m = const ~ts:2 "M" ity in
  let n = const ~ts:2 "N" ity in
  let v = const ~ts:2 "V" ity in
  let r = const ~ts:2 "R" iity in
  Signature.obj_dec
    "eval_app"
    (Term.pi
       [(term_to_var m, tm);
        (term_to_var n, tm);
        (term_to_var v, tm);
        (term_to_var r, Term.pi [(term_to_var (const ~ts:2 "x" ity),tm)] tm);
        (term_to_var (const ~ts:2 "a1" ity), Term.app eval [m;Term.app abs [r]]);
        (term_to_var (const ~ts:2 "a2" ity), Term.app eval [Term.app r [n]; v])]
       (Term.app eval [Term.app app [m;n]; v])) 
    0
    (Signature.Prefix 0)
let eval_abs_decl =
  let r = const ~ts:2 "R" iity in
  Signature.obj_dec
    "eval_abs"
    (Term.pi
       [(term_to_var r, Term.pi [(term_to_var (const ~ts:2 "x" ity),tm)] tm)]
       (Term.app eval [Term.app abs [r]; Term.app abs [r]]))
    0
    (Signature.Prefix 0)

let eval_sig =
  List.fold_left
    Signature.add_obj_decl
    (List.fold_left
       Signature.add_type_decl
       Signature.empty
       [ty_decl; tm_decl; typeof_decl; eval_decl])
    [arrow_decl; app_decl; abs_decl; typeof_app_decl; typeof_abs_decl; eval_app_decl; eval_abs_decl]

let (typeof_schema : Context.ctx_schema) =
  let x = const "x" ity in
  let y = const "y" ity in
  let t = Term.var Term.Logic "T" 1 ity in
   [Context.B([("T",ity)],[(Term.term_to_var x,tm);(Term.term_to_var y,Term.app typeof [x;t])])]
