open OUnit
open Test_helper
open Formula
open Term
open Sequent

let assert_tests =
  "Assert"
  >::: [ ("Assert should succeed when Adelfa can search for solution"
         >:: fun () ->
         let t = var Eigen "T" 1 ity in
         let f1 = atm Context.Nil t tm in
         let seq = Sequent.make_sequent_from_goal ~form:f1 () in
         let assertion = Top in
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_hyp seq f1;
         Prover.set_sequent seq;
         Prover.assert_thm (Uterms.WithDepth 1) assertion;
         assert_equal ~cmp:Formula.eq f1 (Prover.get_sequent ()).goal;
         assert_bool
           "Should add assertion to hyps"
           ((Prover.get_sequent ()).hyps
           |> List.map (fun hyp -> hyp.formula)
           |> List.mem assertion))
       ; ("Assert should change subgoal when Adelfa cannot solve it"
         >:: fun () ->
         let t = var Eigen "T" 1 ity in
         let f1 = atm Context.Nil t tm in
         let seq = Sequent.make_sequent_from_goal ~form:f1 () in
         let assertion = Bottom in
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_hyp seq f1;
         Prover.set_sequent seq;
         Prover.assert_thm (Uterms.WithDepth 1) assertion;
         assert_equal ~cmp:Formula.eq Bottom (Prover.get_sequent ()).goal)
       ; ("Assert should respect depth of 0 when searching"
         >:: fun () ->
         let t1 = var Eigen "T1" 1 ity in
         let t2 = var Eigen "T2" 1 ity in
         let f1 = atm Context.Nil (Term.app Test_helper.app [ t1; t2 ]) tm in
         let seq = Sequent.make_sequent_from_goal ~form:f1 () in
         let assertion = atm Context.Nil t1 tm in
         Sequent.add_var seq (term_to_pair t1);
         Sequent.add_var seq (term_to_pair t2);
         Sequent.add_hyp seq f1;
         Prover.set_sequent seq;
         Prover.assert_thm (Uterms.WithDepth 0) assertion;
         assert_equal ~cmp:Formula.eq assertion (Prover.get_sequent ()).goal)
       ; ("Assert should respect depth greater than 0 when searching"
         >:: fun () ->
         let t1 = var Eigen "T1" 1 ity in
         let t2 = var Eigen "T2" 1 ity in
         let f1 = atm Context.Nil (Term.app Test_helper.app [ t1; t2 ]) tm in
         let seq = Sequent.make_sequent_from_goal ~form:f1 () in
         let assertion = atm Context.Nil t1 tm in
         Sequent.add_var seq (term_to_pair t1);
         Sequent.add_var seq (term_to_pair t2);
         Sequent.add_hyp seq f1;
         Prover.set_sequent seq;
         Prover.assert_thm (Uterms.WithDepth 5) assertion;
         assert_equal ~cmp:Formula.eq f1 (Prover.get_sequent ()).goal;
         assert_bool
           "Should add assertion to hyps"
           ((Prover.get_sequent ()).hyps
           |> List.map (fun hyp -> hyp.formula)
           |> List.mem assertion))
       ]
;;

let tests = "Prover" >::: [ assert_tests ]
