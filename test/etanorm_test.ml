open OUnit
open Core
open Term
open Term.Notations
open Test_helper

let eta_normalize t =
  eta_normalize t

let tests =
  "Eta Normalization" >:::
    [
      "x\\ n x = n" >::
        (fun () ->
          let n = nominal_var "n" iity in
          let x = const ~ts:2 "x" ity in
          assert_term_equal n
                            (eta_normalize ([("x",ity)] // (n ^^ [x]))) );

      "x\\ y\\ n x y = n" >::
        (fun () ->
          let n = nominal_var "n" iiity in
          let x = const ~ts:2 "x" ity in
          let y = const ~ts:2 "y" ity in
          assert_term_equal n
                            (eta_normalize ([("x",ity);("y",ity)] // (n ^^ [x; y])))) ; 

      "x\\ y\\ n y x = x\\ y\\ n y x" >::
        (fun () -> 
          let n = nominal_var "n" iiity in
          let x = const ~ts:2 "x" ity in
          let y = const ~ts:2 "y" ity in
          assert_term_equal ([("x",ity);("y",ity)] // (n ^^ [y; x]))
                            (eta_normalize ([("x",ity);("y",ity)] // (n ^^ [y; x])))) ;

      "x\\ n c x = n c" >::
        (fun () -> 
          let n = nominal_var "n" iiity in
          let x = const ~ts:2 "x" ity in
          let c = const ~ts:0 "c" ity in
          assert_term_equal (n ^^ [c])
                            (eta_normalize ([("x",ity)] // (n ^^ [c; x])))) ;

      "x\\ n (y\\ c y) x = nc" >::
        (fun () ->
          let n = nominal_var "n" (Type.tyarrow [iity;ity] ity) in 
          let x = const ~ts:2 "x" iity in
          let y = const ~ts:2 "y" ity in
          let c = const ~ts:0 "c" iity in
          assert_term_equal
            (n ^^ [c])
            (eta_normalize ([("x",ity)] // (n ^^ [([("y",ity)] // (c ^^ [y])); x])))) ;
    ]
