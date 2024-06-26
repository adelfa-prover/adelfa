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
            "Prefix doesn't allow types which subordinate passed in types"
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
       ; ("Alpha conversion"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let b1 = C.B ([], [ Term.term_to_var n, tm ]) in
          let b2 = C.B ([], [ Term.term_to_var n1, tm ]) in
          assert_bool
            "Block restriction"
            (C.block_eq_sub unique_sub_rel typeof_decl.ty_name b1 b2))
       ; ("Alpha conversion doesn't map two variables to the same variable"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let n2 = Term.nominal_var "n2" ity in
          let b1 = C.B ([], [ Term.term_to_var n, tm; Term.term_to_var n2, tm ]) in
          let b2 = C.B ([], [ Term.term_to_var n1, tm; Term.term_to_var n1, tm ]) in
          assert_bool
            "Two variables mapped to the same one"
            (C.block_eq_sub unique_sub_rel typeof_decl.ty_name b1 b2 |> not))
       ; ("Alpha conversion doesn't map a variable twice"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let n2 = Term.nominal_var "n2" ity in
          let b1 = C.B ([], [ Term.term_to_var n, tm; Term.term_to_var n, tm ]) in
          let b2 = C.B ([], [ Term.term_to_var n1, tm; Term.term_to_var n2, tm ]) in
          assert_bool
            "Variable mapped to two different variables"
            (C.block_eq_sub unique_sub_rel typeof_decl.ty_name b1 b2 |> not))
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
          let entries' =
            [ Term.term_to_var n1, tm
            ; Term.term_to_var n2, ty
            ; Term.term_to_var n, Term.App (typeof, [ n1; n2 ])
            ]
          in
          let b1 = C.B ([], entries) in
          let b2 = C.B ([], entries') in
          assert_bool
            "Block restriction"
            (C.block_eq_sub unique_sub_rel typeof_decl.ty_name b1 b2))
       ; ("Alpha conversion with arity types"
          >:: fun () ->
          let a = Term.var Logic "A" 1 ity in
          let b = Term.var Logic "B" 1 ity in
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let entries =
            [ Term.term_to_var n, tm; Term.term_to_var n1, Term.App (typeof, [ n; a ]) ]
          in
          let entries' =
            [ Term.term_to_var n, tm; Term.term_to_var n1, Term.App (typeof, [ n; b ]) ]
          in
          let b1 = C.B ([ "A", ity ], entries) in
          let b2 = C.B ([ "B", ity ], entries') in
          assert_bool
            "Block restriction"
            (C.block_eq_sub unique_sub_rel typeof_decl.ty_name b1 b2))
       ]
;;

let tests = "Context" >::: [ prefix; block; equality ]
