open OUnit
open Test_helper
open Formula
open Term

let block_sim =
  "Block similarity"
  >::: [ ("Block similarity"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m tm in
          let b1 = Context.B ([], [ term_to_var n, tm ]) in
          let b2 = Context.B ([], [ term_to_var n, tm ]) in
          let res = Formula.block_sim f "g" unique_sub_rel b1 b2 in
          assert_bool "Blocks should be similar" res)
       ; ("Block sim fail"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m tm in
          let b1 = Context.B ([], [ term_to_var n, tm ]) in
          let b2 = Context.B ([], [ term_to_var n, ty ]) in
          let res = Formula.block_sim f "g" unique_sub_rel b1 b2 in
          assert_bool "Blocks should not be similar" (not res))
       ; ("Block sim subordination"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let n1 = nominal_var "n1" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m ty in
          let b1 = Context.B ([], [ term_to_var n, ty; term_to_var n1, tm ]) in
          let b2 = Context.B ([], [ term_to_var n, ty ]) in
          let res = Formula.block_sim f "g" unique_sub_rel b1 b2 in
          assert_bool "Blocks should be similar" res)
       ; ("Block sim subordination failure"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let n1 = nominal_var "n1" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m tm in
          let b1 = Context.B ([], [ term_to_var n, ty; term_to_var n1, tm ]) in
          let b2 = Context.B ([], [ term_to_var n, ty ]) in
          let res = Formula.block_sim f "g" unique_sub_rel b1 b2 in
          assert_bool "Blocks should not be similar" (not res))
       ; ("Block sim subordination failure from explicit portion"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm (Context.Ctx (g, (term_to_var n, tm))) m tm in
          let b1 = Context.B ([], []) in
          let b2 = Context.B ([], []) in
          let res = Formula.block_sim f "g" unique_sub_rel b1 b2 in
          assert_bool "Blocks should not be similar" (not res))
       ]
;;

let block_in =
  "Block in schema"
  >::: [ ("Block in simple"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m tm in
          let b1 = Context.B ([], [ term_to_var n, tm ]) in
          let schema = [ Context.B ([], [ term_to_var n, tm ]) ] in
          let res = Formula.block_in_schema_sub f "g" unique_sub_rel b1 schema in
          assert_bool "Blocks should be in schema" res)
       ; ("Block in allows subordination if prefix"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let n1 = nominal_var "n1" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m ty in
          let b1 = Context.B ([], [ term_to_var n, ty; term_to_var n1, tm ]) in
          let schema = [ Context.B ([], [ term_to_var n, ty ]) ] in
          let res = Formula.block_in_schema_sub f "g" unique_sub_rel b1 schema in
          assert_bool "Blocks should be in schema" res)
       ; ("Block in prohibits subordination if not prefix"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let n1 = nominal_var "n1" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m ty in
          let b1 = Context.B ([], [ term_to_var n, ty ]) in
          let schema = [ Context.B ([], [ term_to_var n, ty; term_to_var n1, tm ]) ] in
          let res = Formula.block_in_schema_sub f "g" unique_sub_rel b1 schema in
          assert_bool "Blocks should be in schema" (not res))
       ]
;;

let schema_transport =
  "Schema transport"
  >::: [ ("Schema transports to self"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m tm in
          let schema = [ Context.B ([], [ term_to_var n, tm ]) ] in
          let res = Formula.schema_transports f "g" unique_sub_rel schema schema in
          assert_bool "Blocks should be in schema" res)
       ; ("Schema transports to smaller ctx"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m tm in
          let schema1 =
            [ Context.B ([], [ term_to_var n, tm ])
            ; Context.B ([], [ term_to_var n, ty ])
            ]
          in
          let schema2 = [ Context.B ([], [ term_to_var n, tm ]) ] in
          let res = Formula.schema_transports f "g" unique_sub_rel schema1 schema2 in
          assert_bool "Blocks should be in schema" res)
       ]
;;

let tests = "Formula" >::: [ block_sim; block_in; schema_transport ]
