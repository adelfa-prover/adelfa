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
       ; ("Block sim fail from formula type"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let n1 = nominal_var "n1" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m tm in
          let b1 = Context.B ([], [ term_to_var n, tm ]) in
          let b2 = Context.B ([], [ term_to_var n, tm; term_to_var n1, tm ]) in
          let res = Formula.block_sim f "g" unique_sub_rel b1 b2 in
          assert_bool "Blocks should not be similar" (not res))
       ; ("Block sim fail from formula type"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let m = var Eigen "M" 0 ity in
          let f = atm g m tm in
          let b1 = Context.B ([], []) in
          let b2 = Context.B ([], [ term_to_var n, tm ]) in
          let res = Formula.block_sim f "g" unique_sub_rel b1 b2 in
          assert_bool "Blocks should not be similar" (not res))
       ; ("Block sim fail from formula type 2"
          >:: fun () ->
          let g = Context.Var "g" in
          let n = nominal_var "n" ity in
          let m = var Eigen "N" 0 ity in
          let f = atm g m nat in
          let b1 = Context.B ([], []) in
          let b2 = Context.B ([], [ term_to_var n, nat ]) in
          let res = Formula.block_sim f "g" nat_sub_rel b1 b2 in
          assert_bool "Blocks should not be similar" (not res))
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
          let res =
            Formula.block_in_schema_sub
              ~dest_block:b1
              ~src_schema:schema
              f
              "g"
              unique_sub_rel
          in
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
          let res =
            Formula.block_in_schema_sub
              ~dest_block:b1
              ~src_schema:schema
              f
              "g"
              unique_sub_rel
          in
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
          let res =
            Formula.block_in_schema_sub
              ~dest_block:b1
              ~src_schema:schema
              f
              "g"
              unique_sub_rel
          in
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
          let res =
            Formula.schema_transports
              unique_sub_rel
              ~ctx_var:"g"
              ~src_schema:schema
              ~dest_schema:schema
              f
          in
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
          let res =
            Formula.schema_transports
              ~ctx_var:"g"
              ~src_schema:schema1
              ~dest_schema:schema2
              unique_sub_rel
              f
          in
          assert_bool "Blocks should be in schema" res)
       ]
;;

let negative_occurrences =
  "Negative occurrences"
  >::: [ ("Negative occurrences"
          >:: fun () ->
          let g1 = Context.ctx_var "G" in
          let e1 = var Eigen "E1" 0 ity in
          let f = imp (atm (Context.Var g1) e1 tm) Bottom in
          assert_bool "Should have a negative occurrence of G" (occurs_negatively g1 f))
       ; ("No occurrence"
          >:: fun () ->
          let f = Bottom in
          assert_bool
            "Should not have a negative occurrence of a variable which doesn't appear in \
             a formula"
            (occurs_negatively "G" f |> not))
       ; ("Negative occurrence of other variable"
          >:: fun () ->
          let g1 = Context.ctx_var "G" in
          let e1 = var Eigen "E1" 0 ity in
          let f = imp (atm (Context.Var g1) e1 tm) Bottom in
          assert_bool
            "Should not have a negative occurrence of a variable which doesn't appear in \
             a formula"
            (occurs_negatively "F" f |> not))
       ; ("Negative occurrence of bottom"
          >:: fun () ->
          let g1 = Context.ctx_var "G" in
          let e1 = var Eigen "E1" 0 ity in
          let f = imp Bottom (atm (Context.Var g1) e1 tm) in
          assert_bool
            "Should hold for a formula which has a vacuously true statement"
            (occurs_negatively "F" f))
       ; ("Positive occurrence of top"
          >:: fun () ->
          let g1 = Context.ctx_var "G" in
          let e1 = var Eigen "E1" 0 ity in
          let f = imp (atm (Context.Var g1) e1 tm) Top in
          assert_bool
            "Should hold for a formula which has a true in a positive position"
            (occurs_negatively "F" f))
       ; ("Holds when both children of AND have negative occurrence"
          >:: fun () ->
          let g1 = Context.ctx_var "G" in
          let e1 = var Eigen "E1" 0 ity in
          let f =
            f_and
              (imp (atm (Context.Var g1) e1 tm) Bottom)
              (imp (atm (Context.Var g1) e1 tm) Bottom)
          in
          assert_bool
            "Should hold for a formula which has negative on both sides of and"
            (occurs_negatively "G" f))
       ; ("Doesn't hold when only one child of AND has negative occurrence"
          >:: fun () ->
          let g1 = Context.ctx_var "G" in
          let e1 = var Eigen "E1" 0 ity in
          let f =
            f_and (imp (atm (Context.Var g1) e1 tm) Bottom) (atm (Context.Var g1) e1 tm)
          in
          assert_bool
            "Should hold for a formula which has negative on both sides of and"
            (occurs_negatively "G" f |> not))
       ; ("Holds when either child of OR has negative occurrence"
          >:: fun () ->
          let g1 = Context.ctx_var "G" in
          let f1 = Context.ctx_var "F" in
          let e1 = var Eigen "E1" 0 ity in
          let f =
            f_or
              (imp (atm (Context.Var g1) e1 tm) Bottom)
              (imp (atm (Context.Var f1) e1 tm) Bottom)
          in
          let () = assert_bool "Should hold" (occurs_negatively "G" f) in
          let f =
            f_or
              (imp (atm (Context.Var f1) e1 tm) Bottom)
              (imp (atm (Context.Var g1) e1 tm) Bottom)
          in
          assert_bool "Should hold" (occurs_negatively "F" f))
       ; ("Doesn't hold when neither child of OR has negative occurrence"
          >:: fun () ->
          let f1 = Context.ctx_var "F" in
          let e1 = var Eigen "E1" 0 ity in
          let f =
            f_or
              (imp (atm (Context.Var f1) e1 tm) Bottom)
              (imp (atm (Context.Var f1) e1 tm) Bottom)
          in
          assert_bool "Should not hold" (occurs_negatively "G" f |> not))
       ; ("Holds when assumption formula is provably false"
          >:: fun () ->
          let g1 = Context.ctx_var "G1" in
          let e1 = var Eigen "E1" 0 ity in
          let hyp = imp Top Bottom in
          let f = imp hyp (atm (Context.Var g1) e1 tm) in
          assert_bool "Should hold" (occurs_negatively "G1" f))
       ; ("Holds when assumption formula has occurrence in positive position"
          >:: fun () ->
          let g1 = Context.ctx_var "G1" in
          let e1 = var Eigen "E1" 0 ity in
          let hyp = imp Top (atm (Context.Var g1) e1 tm) in
          let f = imp hyp (atm (Context.Var g1) e1 tm) in
          assert_bool "Should hold" (occurs_negatively "G1" f))
       ; ("Does not hold when assumption formula has no occurrence in positive"
          >:: fun () ->
          let g1 = Context.ctx_var "G1" in
          let g2 = Context.ctx_var "G2" in
          let e1 = var Eigen "E1" 0 ity in
          let hyp = imp Top (atm (Context.Var g2) e1 tm) in
          let f = imp hyp (atm (Context.Var g1) e1 tm) in
          assert_bool "Should not hold" (occurs_negatively "G1" f |> not))
       ; ("Avoids shadowing"
          >:: fun () ->
          let g1 = Context.ctx_var "G1" in
          let e1 = var Eigen "E1" 0 ity in
          let hyp = ctx [ "G1", "c" ] (imp Top (atm (Context.Var g1) e1 tm)) in
          let f = imp hyp (atm (Context.Var g1) e1 tm) in
          assert_bool "Should not hold" (occurs_negatively "G1" f |> not))
       ; ("Avoids shadowing, considering bottom"
          >:: fun () ->
          let g1 = Context.ctx_var "G1" in
          let e1 = var Eigen "E1" 0 ity in
          let hyp = ctx [ "G1", "c" ] (imp Top Bottom) in
          let f = imp hyp (atm (Context.Var g1) e1 tm) in
          assert_bool "Should hold" (occurs_negatively "G1" f))
       ; ("Avoids shadowing, considering top"
          >:: fun () ->
          let g1 = Context.ctx_var "G1" in
          let e1 = var Eigen "E1" 0 ity in
          let hyp = ctx [ "G1", "c" ] (imp Top (imp Top Bottom)) in
          let f = imp hyp (atm (Context.Var g1) e1 tm) in
          assert_bool "Should hold" (occurs_negatively "G1" f))
       ]
;;

let empty_schema = [ Context.B ([], []) ]
let nat_schema = [ Context.B ([], [ term_to_var (Term.var Constant "x" 1 ity), nat ]) ]

let context_subsumption =
  "Context subsumption"
  >::: [ ("Context subsumption"
          >:: fun () ->
          let g1 = Context.Var "G1" in
          let num = var Eigen "N" 0 ity in
          let f = ctx [ "G1", "c" ] (imp (atm g1 num nat) Bottom) in
          let res =
            schema_transports
              ~ctx_var:"G1"
              nat_sub_rel
              ~src_schema:empty_schema
              ~dest_schema:nat_schema
              f
          in
          assert_bool "Should not hold" (not res))
       ; ("Should not be compatible"
          >:: fun () ->
          let g1 = Context.Var "G1" in
          let num = var Eigen "N" 0 ity in
          let f = ctx [ "G1", "C" ] (imp (atm g1 num nat) Bottom) in
          let res =
            get_compatible_context_schemas
              [ "C'", nat_schema; "C", empty_schema ]
              nat_sub_rel
              f
          in
          let are_compatible = List.assoc_opt "G1" res in
          assert_bool
            "Should have an entry for ctx var G1"
            (Option.is_some are_compatible);
          let r = Option.fold ~none:false ~some:(List.mem "C'") are_compatible in
          assert_bool "C should not be compatible with C'" (not r))
       ]
;;

let tests =
  "Formula"
  >::: [ block_sim
       ; block_in
       ; schema_transport
       ; negative_occurrences
       ; context_subsumption
       ]
;;
