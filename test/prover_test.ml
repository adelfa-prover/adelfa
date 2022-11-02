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

let state_tests =
  "State"
  >::: [ ("Snapshotting replaces sequent"
         >:: fun () ->
         let s = Sequent.make_sequent_from_goal ~form:Bottom () in
         Prover.set_sequent s;
         let old = State.snapshot () in
         (Prover.get_sequent ()).goal <- Top;
         assert_formula_equal (Prover.get_sequent ()).goal Top;
         State.reload old;
         assert_formula_equal (Prover.get_sequent ()).goal Bottom)
       ; ("Snapshotting and setting a new sequent restores old one"
         >:: fun () ->
         let s = Sequent.make_sequent_from_goal ~form:Bottom () in
         let s' = Sequent.make_sequent_from_goal ~form:Top () in
         Prover.set_sequent s;
         let old = State.snapshot () in
         Prover.set_sequent s';
         assert_formula_equal (Prover.get_sequent ()).goal Top;
         State.reload old;
         assert_formula_equal (Prover.get_sequent ()).goal Bottom)
       ]
;;

let nominal_renamed_in_lemma () =
  let e = var Eigen "E" 0 ity in
  let x = const "x" ity in
  let n = nominal_var "n" ity in
  let g = Context.ctx_var "G" in
  let g1 = Context.ctx_var "G1" in
  let schema = Context.CtxTy ("c", [ [ term_to_var x, tm ] ]) in
  let lemma =
    Formula.forall
      [ "E", ity ]
      (Formula.imp
         (Formula.atm (Context.Ctx (Context.Var g, (term_to_var n, tm))) e tm)
         Formula.Bottom)
  in
  Prover.add_lemma "lemma" lemma;
  let s = Sequent.make_sequent_from_goal ~form:Formula.Bottom () in
  Sequent.add_hyp
    s
    ~name:"H1"
    (Formula.atm (Context.Ctx (Context.Var g1, (term_to_var n, tm))) e tm);
  Sequent.add_ctxvar s g schema;
  Sequent.add_ctxvar s g1 schema;
  Prover.set_sequent s;
  let exn = Failure (Unify.explain_failure Unify.Generic) in
  assert_raises exn (fun () -> Prover.apply "lemma" [ "H1" ] [])
;;

let nominal_same_in_seq () =
  let e = var Eigen "E" 0 ity in
  let x = const "x" ity in
  let n = nominal_var "n" ity in
  let g = Context.ctx_var "G" in
  let schema = Context.CtxTy ("c", [ [ term_to_var x, tm ] ]) in
  let lemma =
    Formula.forall
      [ "E", ity ]
      (Formula.imp
         (Formula.atm (Context.Ctx (Context.Var g, (term_to_var n, tm))) e tm)
         Formula.Bottom)
  in
  let s = Sequent.make_sequent_from_goal ~form:Formula.Bottom () in
  Sequent.add_hyp
    s
    ~name:"H1"
    (Formula.atm (Context.Ctx (Context.Var g, (term_to_var n, tm))) e tm);
  Sequent.add_hyp s ~name:"H2" lemma;
  Sequent.add_ctxvar s g schema;
  Prover.set_sequent s;
  assert_equal () (Prover.apply "H2" [ "H1" ] [])
;;

let apply_tests =
  "Apply"
  >::: [ "Renames nominals appearing in lemmas" >:: nominal_renamed_in_lemma
       ; "Keeps nominal names appearing in sequent" >:: nominal_same_in_seq
       ]
;;

let tests = "Prover" >::: [ assert_tests; apply_tests ]
