open OUnit
open Term
open Term.Notations
open Unify
open Test_helper



let left_unify ?(used=[]) t1 t2 =
    (*  assert_ty_equal (tc [] t1) (tc [] t2) ;*)
    left_unify ~used t1 t2
    
let tests =
  "Unify" >:::
    [
      "Eigen variables on left should not unify with nominal variables" >::
        (fun () ->
           let a = var Eigen ("a") 1 Test_helper.ity in
           let n = nominal_var ("n") ity in
             assert_raises_any
               (fun () -> left_unify a n)) ;

      "Raised eigen variables on left should unify with nominal variables" >::
        (fun () ->
           let a = var Eigen ("a") 1 iity in
           let n = nominal_var ("n") ity in
           let used = [("n",n)] in
           left_unify ~used (a ^^ [n]) n ;
           assert_term_equal ([(get_id ityvar, ity)]// db 1) a) ;

      "Pruning should not generate a needless new name" >::
        (fun () ->
           let n = nominal_var ("n") ity in
           let a = var Eigen ("A") 1 (Type.tyarrow [ity] aty) in
           let b = var Eigen ("B") 1 aty in
           let used = [("n", n);
                       ("A", a);
                       ("B", b)] in
             left_unify ~used (a ^^ [n]) b ;
             assert_term_pprint_equal "[x1]B" a ;
             assert_term_pprint_equal "B" b) ;

      "X^0 a^1 b^1 = Y^0 Z^0 b^1" >::
        (fun () ->
           let a = const ~ts:2 ("a") aty in
           let b = const ~ts:2 ("b") bty in
           let x = var Eigen ("X") 1 (Type.tyarrow [aty; bty] ity) in
           let y = var Eigen ("Y") 1 (Type.tyarrow [cty; bty] ity) in
           let z = var Eigen ("Z") 1 cty in
           let used = [("X", x);
                       ("Y", y);
                       ("Z", z);
                       ("a", a);
                       ("b", b)] in
             left_unify ~used (x ^^ [a;b]) (y ^^ [z;b]) ;
             assert_term_pprint_equal "[x1][x2]Y Z x2" x ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

      "X^0 a^1 = Y^0 (Z^0 a^1)" >::
        (fun () ->
           let a = const ~ts:2 ("a") ity in
           let x = var Eigen ("X") 1 iity in
           let y = var Eigen ("Y") 1 iity in
           let z = var Eigen ("Z") 1 iity in
           let used = [("a", a);
                       ("X", x);
                       ("Y", y);
                       ("Z", z)] in
             left_unify ~used (x ^^ [a]) (y ^^ [z ^^ [a]]) ;
             assert_term_pprint_equal "[x1]Y (Z x1)" x ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

      "w\\X^0 w = Y^0 Z^0" >::
        (fun () ->
           let x = var Eigen ("X") 1 iity in
           let y = var Eigen ("Y") 1 iiity in
           let z = var Eigen ("Z") 1 ity in
           let used = [("X", x);
                       ("Y", y);
                       ("Z", z)] in
             left_unify ~used ([("w",ity)] // (x ^^ [db 1])) (y ^^ [z]) ;
             assert_term_pprint_equal "[x1]Y Z x1" x ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

      "X^0 a^1 = app (Y^0 W^0 a^1) (Z^0 a^1)" >::
        (fun () ->
           let a = const ~ts:2 ("a") aty in
           let x = var Eigen ("X") 1 (Type.tyarrow [aty] ity) in
           let y = var Eigen ("Y") 1 (Type.tyarrow [bty; aty] cty) in
           let z = var Eigen ("Z") 1 (Type.tyarrow [aty] dty) in
           let w = var Eigen ("W") 1 bty in
           let capp = const ~ts:0 ("app") (Type.tyarrow [cty; dty] ity) in
           let used = [("a", a);
                       ("X", x); 
                       ("Y", y);
                       ("Z", z);
                       ("W", w)] in
             left_unify ~used
               (x ^^ [a])
               (capp ^^ [y ^^ [w;a]; z ^^ [a]]) ;
             assert_term_pprint_equal "[x1]app (Y W x1) (Z x1)" x ;
             assert_term_pprint_equal "W" w ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

      "f\\x\\f x = f\\x\\f (Z f x)" >::
        (fun () ->
           let z = var Eigen ("Z") 1 (Type.tyarrow [iity; ity] ity) in
           let used = [("Z", z)]
           in
             left_unify ~used
               ([("x",iity);
                 ("f",ity)] //
                  (db 2 ^^ [db 1]))
               ([("x",iity);
                 ("f",ity)] //
                  (db 2 ^^ [z ^^ [db 2; db 1]])) ;
           assert_term_pprint_equal "[x1][x2]x2" z) ;
      
      "Raised eta-long form should unify" >::
        (fun () ->
           let a = var Eigen ("a") 1 (Type.tyarrow [iity] iity) in
           let x = const ~ts:2 ("x") ity in
           let n = nominal_var ("n") iity in
           let c = const ~ts:0 ("c") ity in
           let used = [("x", x); ("n", n); ("a", a); ("c", c)] in
           left_unify ~used (a ^^ [[("x", ity)] // (n ^^ [x])]) n;
           assert_term_equal ([("z1",iity)] // db 1) a) ;

      "Unification within types" >::
        (fun () ->
         let a = const ~ts:0 "a" iity in
         let b = const ~ts:0 "b" ity in
         let c = const ~ts:0 "c" ity in
         let x = const ~ts:2 "x" ity in
         let y = var Eigen "y" 1 ity in
         let ty1 = pi [(term_to_var x, (Term.app a [y]))] b in
         let ty2 = pi [(term_to_var x, (Term.app a [c]))] b in
         left_unify ty1 ty2;
         assert_term_equal c y) ;

      "eta-long unification" >::
        (fun () ->
         let r = var Eigen "R" 1 iity in
         let t = var Eigen "T" 1 ity in
         let u = var Eigen "U" 1 ity in
         let t1 = Term.app
                    typeof
                    [(Term.app abs [u;(lambda [("z",ity)] (Term.app r [db 1]))]);
                     (Term.app arrow [u;t])]
         in
         let e = var Eigen "E" 1 ity in
         let ty = var Eigen "Ty" 1 ity in
         let t2 = Term.app typeof [e;ty] in
         left_unify t1 t2;
         assert_term_pprint_equal (Print.string_of_term (abs ^^ [u;[("x1",ity)] // (r ^^ [db 1])])) e
        ) ;
    ]
