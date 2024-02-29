open OUnit
open Test_helper
module C = Context

let block = "Blocks" >::: []

let prefix =
  "Context prefix"
  >::: [ ("Refl"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let b1 = C.B ([], [ Term.term_to_var n, tm ]) in
          assert_bool
            "Block is prefix of itself"
            (C.block_prefix_sub unique_sub_rel [] b1 b1))
       ; ("Prefix 1"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let b1 = C.B ([], [ Term.term_to_var n, tm; Term.term_to_var n1, ty ]) in
          let b2 = C.B ([], [ Term.term_to_var n, tm ]) in
          assert_bool
            "Larger block is not prefix"
            (not (C.block_prefix_sub unique_sub_rel [] b1 b2)))
       ; ("Prefix 2"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let b1 = C.B ([], [ Term.term_to_var n, tm ]) in
          let b2 = C.B ([], [ Term.term_to_var n, tm; Term.term_to_var n1, ty ]) in
          assert_bool
            "Smaller block is prefix"
            (C.block_prefix_sub unique_sub_rel [] b1 b2))
       ; ("Prefix doesn't allow for extra items that subordinate passed in type"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let b1 = C.B ([], [ Term.term_to_var n, tm ]) in
          let b2 = C.B ([], [ Term.term_to_var n, tm; Term.term_to_var n1, ty ]) in
          assert_bool
            "Prefix should not pass"
            (not (C.block_prefix_sub unique_sub_rel [ ty_decl.ty_name ] b1 b2)))
       ]
;;

let equality =
  "Context equality"
  >::: [ ("Reflexivity"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let entries = [ Term.term_to_var n, tm ] in
          let b1 = C.B ([], entries) in
          let b2 = C.B ([], entries) in
          assert_bool
            "Block equality reflexive"
            (C.block_eq_sub unique_sub_rel tm_decl.ty_name b1 b2))
       ; ("Restriction"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let entries = [ Term.term_to_var n, tm ] in
          let b1 = C.B ([], entries) in
          let b2 = C.B ([], []) in
          assert_bool
            "Block restriction"
            (C.block_eq_sub unique_sub_rel ty_decl.ty_name b1 b2))
       ; ("Half restricted"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let entries = [ Term.term_to_var n, tm; Term.term_to_var n1, ty ] in
          let b1 = C.B ([], entries) in
          let b2 = C.B ([], [ Term.term_to_var n1, ty ]) in
          assert_bool
            "Block restriction"
            (C.block_eq_sub unique_sub_rel ty_decl.ty_name b1 b2))
       ; ("Entry with dependencies"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let n2 = Term.nominal_var "n2" ity in
          let entries =
            [ Term.term_to_var n, tm
            ; Term.term_to_var n1, ty
            ; Term.term_to_var n2, Term.App (typeof, [ n; n1 ])
            ]
          in
          let b1 = C.B ([], entries) in
          let b2 = C.B ([], [ Term.term_to_var n1, ty ]) in
          assert_bool
            "Block restriction"
            (C.block_eq_sub unique_sub_rel ty_decl.ty_name b1 b2))
       ; ("Alpha conversion with dependencies"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let n2 = Term.nominal_var "n2" ity in
          let entries =
            [ Term.term_to_var n, tm
            ; Term.term_to_var n1, ty
            ; Term.term_to_var n2, Term.App (typeof, [ n; n1 ])
            ]
          in
          let b1 = C.B ([], entries) in
          let b2 = C.B ([], entries) in
          assert_bool
            "Block restriction"
            (C.block_eq_sub unique_sub_rel typeof_decl.ty_name b1 b2))
       ]
;;

let tests = "Context" >::: [ prefix; block; equality ]
