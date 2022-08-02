open OUnit
open Test_helper
open Term
open Formula
open Tactics

let assert_expected_cases n cases =
  assert_failure
    (Printf.sprintf "Expected %d case(s) but found %d case(s)" n (List.length cases))
;;

let case_tests =
  "Case"
  >::: [ ("Normal"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let p = var Eigen "P" 0 ity in
         let term = atm Context.Nil p (Term.app eval [ a; b ]) in
         let seq = Sequent.make_sequent_from_goal ~form:Bottom () in
         Sequent.add_hyp seq ~name:"H1" term;
         match cases eval_sig [] seq "H1" with
         | [ case1; case2 ] ->
           set_bind_state case1.bind_state_case;
           assert_pprint_equal "{eval_abs A : eval (abs A) (abs A)}" term;
           set_bind_state case2.bind_state_case;
           assert_pprint_equal "{eval_app A A1 B P P1 P2 : eval (app A A1) B}" term
         | cases -> assert_expected_cases 2 cases)
         (* "With Contexts" >:: *)
         (*   (fun () -> *)
         (*    let e = var Eigen "E" 0 ity in *)
         (*    let ty = var Eigen "Ty" 0 ity in *)
         (*    let p = var Eigen "P" 0 ity in *)
         (*    let l = Context.ctx_var "L" in  *)
         (*    let term = atm (Context.Var "L") p (Term.app typeof [e;ty]) in *)
         (*    let seq = Sequent.make_sequent_from_goal Bottom in  *)
         (*    Sequent.add_var seq ("E",e); *)
         (*    Sequent.add_var seq ("Ty",ty); *)
         (*    Sequent.add_var seq ("P",p); *)
         (*    Sequent.add_hyp seq ~name:"H1" term; *)
         (*    Sequent.add_ctxvar seq l (Context.CtxTy("c",[])); *)
         (*    match cases eval_sig [("c",typeof_schema)] seq "H1" with *)
         (*    | [case1;case2;case3] -> *)
         (*       set_bind_state case1.bind_state_case ; *)
         (*      assert_pprint_equal *)
         (*        "{L |- typeof_abs E1 Ty1 Ty2 P1 : typeof (abs ([x1]E1 x1)) (arrow Ty1 Ty2)}" *)
         (*        term ; *)
         (*       set_bind_state case2.bind_state_case ; *)
         (*       assert_pprint_equal *)
         (*         "{L |- typeof_app E1 E2 Ty P1 P2 P3 : typeof (app E1 E2) Ty}" *)
         (*         term; *)
         (*       set_bind_state case3.bind_state_case ; *)
         (*       assert_pprint_equal *)
         (*         "{L |- n1 : typeof n T}" *)
         (*         term *)
         (*    | cases -> assert_expected_cases 3 cases *)
         (*   ) ; *)
       ]
;;

let apply_tests =
  "Apply"
  >::: [ ("Normal"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let t = var Eigen "T" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm Context.Nil p4 (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm
               Context.Nil
               p5
               (Term.app typeof [ Term.app abs [ r ]; Term.app arrow [ s; t ] ])
           ]
         in
         (* let f_res = apply [] seq f args in *)
         let vwiths =
           [ "A", Term.app abs [ r ]
           ; "B", Term.app abs [ r ]
           ; "C", Term.app arrow [ s; t ]
           ; "P1", p4
           ; "P2", p5
           ]
         in
         let f_res = apply_with [] seq f args (vwiths, []) in
         assert_pprint_equal "exists P3, {P3 : typeof (abs R) (arrow S T)}" f_res)
       ; ("Properly restricted"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let t = var Eigen "T" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm ~ann:(LT 1) Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm
               ~ann:(LT 1)
               Context.Nil
               p4
               (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm
               Context.Nil
               p5
               (Term.app typeof [ Term.app abs [ r ]; Term.app arrow [ s; t ] ])
           ]
         in
         (* let f_res = apply [] seq f args in *)
         let vwiths =
           [ "A", Term.app abs [ r ]
           ; "B", Term.app abs [ r ]
           ; "C", Term.app arrow [ s; t ]
           ; "P1", p4
           ; "P2", p5
           ]
         in
         let f_res = apply_with [] seq f args (vwiths, []) in
         assert_pprint_equal "exists P3, {P3 : typeof (abs R) (arrow S T)}" f_res)
       ; ("Needlessly restricted"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let t = var Eigen "T" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm
               ~ann:(LT 1)
               Context.Nil
               p4
               (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm
               Context.Nil
               p5
               (Term.app typeof [ Term.app abs [ r ]; Term.app arrow [ s; t ] ])
           ]
         in
         (* let f_res = apply [] seq f args in *)
         let vwiths =
           [ "A", Term.app abs [ r ]
           ; "B", Term.app abs [ r ]
           ; "C", Term.app arrow [ s; t ]
           ; "P1", p4
           ; "P2", p5
           ]
         in
         let f_res = apply_with [] seq f args (vwiths, []) in
         assert_pprint_equal "exists P3, {P3 : typeof (abs R) (arrow S T)}" f_res)
       ; ("Improperly restricted"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let t = var Eigen "T" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm ~ann:(LT 1) Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm Context.Nil p4 (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm
               Context.Nil
               p5
               (Term.app typeof [ Term.app abs [ r ]; Term.app arrow [ s; t ] ])
           ]
         in
         (* assert_raises (Failure "Inductive restriction violated") *)
         (*               (fun () -> apply [] seq f args) ) ; *)
         let vwiths =
           [ "A", Term.app abs [ r ]
           ; "B", Term.app abs [ r ]
           ; "C", Term.app arrow [ s; t ]
           ; "P1", p4
           ; "P2", p5
           ]
         in
         assert_raises (Failure "Inductive restriction violated") (fun () ->
           apply_with [] seq f args (vwiths, [])))
       ; ("Improperly restricted (2)"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let t = var Eigen "T" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm ~ann:(LT 1) Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm
               ~ann:(EQ 1)
               Context.Nil
               p4
               (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm
               Context.Nil
               p5
               (Term.app typeof [ Term.app abs [ r ]; Term.app arrow [ s; t ] ])
           ]
         in
         (* assert_raises (Failure "Inductive restriction violated") *)
         (*               (fun () -> apply [] seq f args) ) ; *)
         let vwiths =
           [ "A", Term.app abs [ r ]
           ; "B", Term.app abs [ r ]
           ; "C", Term.app arrow [ s; t ]
           ; "P1", p4
           ; "P2", p5
           ]
         in
         assert_raises (Failure "Inductive restriction violated") (fun () ->
           apply_with [] seq f args (vwiths, [])))
       ; ("Properly double restricted"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let t = var Eigen "T" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm ~ann:(EQ 1) Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm ~ann:(LT 2) Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm
               ~ann:(EQ 1)
               Context.Nil
               p4
               (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm
               ~ann:(LT 2)
               Context.Nil
               p5
               (Term.app typeof [ Term.app abs [ r ]; Term.app arrow [ s; t ] ])
           ]
         in
         (* let f_res = apply [] seq f args in *)
         let vwiths =
           [ "A", Term.app abs [ r ]
           ; "B", Term.app abs [ r ]
           ; "C", Term.app arrow [ s; t ]
           ; "P1", p4
           ; "P2", p5
           ]
         in
         let f_res = apply_with [] seq f args (vwiths, []) in
         assert_pprint_equal "exists P3, {P3 : typeof (abs R) (arrow S T)}" f_res)
       ; ("Improperly double restricted"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let t = var Eigen "T" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm ~ann:(EQ 1) Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm ~ann:(LT 2) Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm
               ~ann:(EQ 1)
               Context.Nil
               p4
               (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm
               ~ann:(EQ 2)
               Context.Nil
               p5
               (Term.app typeof [ Term.app abs [ r ]; Term.app arrow [ s; t ] ])
           ]
         in
         (* assert_raises (Failure "Inductive restriction violated") *)
         (*               (fun () -> apply [] seq f args) ) ; *)
         let vwiths =
           [ "A", Term.app abs [ r ]
           ; "B", Term.app abs [ r ]
           ; "C", Term.app arrow [ s; t ]
           ; "P1", p4
           ; "P2", p5
           ]
         in
         assert_raises (Failure "Inductive restriction violated") (fun () ->
           apply_with [] seq f args (vwiths, [])))
       ; ("Improperly double restricted (2)"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let t = var Eigen "T" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm ~ann:(EQ 1) Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm ~ann:(LT 2) Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm Context.Nil p4 (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm
               ~ann:(LT 2)
               Context.Nil
               p5
               (Term.app typeof [ Term.app abs [ r ]; Term.app arrow [ s; t ] ])
           ]
         in
         (* assert_raises (Failure "Inductive restriction violated") *)
         (*               (fun () -> apply [] seq f args ) ) ; *)
         let vwiths =
           [ "A", Term.app abs [ r ]
           ; "B", Term.app abs [ r ]
           ; "C", Term.app arrow [ s; t ]
           ; "P1", p4
           ; "P2", p5
           ]
         in
         assert_raises (Failure "Inductive restriction violated") (fun () ->
           apply_with [] seq f args (vwiths, [])))
       ; ("Failure to unify"
         >:: fun () ->
         let a = var Eigen "A" 0 ity in
         let b = var Eigen "B" 0 ity in
         let c = var Eigen "C" 0 ity in
         let r = var Eigen "R" 0 iity in
         let s = var Eigen "S" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let seq =
           Sequent.make_sequent_from_goal
             ~form:(atm Context.Nil p3 (Term.app typeof [ b; c ]))
             ()
         in
         let f =
           forall
             [ "A", ity; "B", ity; "C", ity; "P1", ity; "P2", ity ]
             (imp
                (atm Context.Nil p1 (Term.app eval [ a; b ]))
                (imp
                   (atm Context.Nil p2 (Term.app typeof [ a; c ]))
                   (Formula.exists
                      [ "P3", ity ]
                      (atm Context.Nil p3 (Term.app typeof [ b; c ])))))
         in
         let args =
           [ atm Context.Nil p4 (Term.app eval [ Term.app abs [ r ]; Term.app abs [ r ] ])
           ; atm Context.Nil p5 (Term.app eval [ Term.app abs [ s ]; Term.app abs [ s ] ])
           ]
         in
         try
           (* let _ = apply [] seq f args in *)
           let vwiths =
             [ "A", Term.app abs [ r ]
             ; "B", Term.app abs [ r ]
             ; "C", Term.app abs [ s ]
             ; "P1", p4
             ; "P2", p5
             ]
           in
           let _ = apply_with [] seq f args (vwiths, []) in
           assert_failure "Expected unification failure"
         with
         | Unify.UnifyFailure Unify.Generic -> ())
       ; ("With contexts"
         >:: fun () ->
         let conc = const "conc" iity in
         let hyp = const "hyp" iity in
         let a1 = var Eigen "A" 0 ity in
         let a2 = var Eigen "A" 0 ity in
         let c1 = var Eigen "C" 0 ity in
         let c2 = var Eigen "C" 0 ity in
         let b = var Eigen "B" 0 ity in
         let p1 = var Eigen "P1" 0 ity in
         let p2 = var Eigen "P2" 0 ity in
         let p3 = var Eigen "P3" 0 ity in
         let p4 = var Eigen "P4" 0 ity in
         let p5 = var Eigen "P5" 0 ity in
         let x = const "x" ity in
         let n = nominal_var "n" ity in
         let n1 = nominal_var "n1" ity in
         let n2 = nominal_var "n2" ity in
         let e = Context.ctx_var "E" in
         let l = Context.ctx_var "L" in
         let seq = Sequent.make_sequent_from_goal ~form:Bottom () in
         let _ =
           Sequent.add_ctxvar seq l (Context.CtxTy ("c", []));
           Sequent.add_ctxvar seq e (Context.CtxTy ("c", []));
           Sequent.add_var seq (term_to_pair n);
           Sequent.add_var seq (term_to_pair n1);
           Sequent.add_var seq (term_to_pair n2)
         in
         let f =
           ctx
             [ "E", "c" ]
             (forall
                [ "A", ity; "C", ity; "P1", ity; "P2", ity ]
                (imp
                   (atm
                      (Context.Ctx (Context.Var e, (term_to_var n, Term.app hyp [ a1 ])))
                      p1
                      (Term.app conc [ c1 ]))
                   (imp
                      (atm (Context.Var e) p2 (Term.app conc [ a1 ]))
                      (Formula.exists
                         [ "P3", ity ]
                         (atm (Context.Var e) p3 (Term.app conc [ c1 ]))))))
         in
         let args =
           [ atm
               (Context.Ctx
                  ( Context.Ctx (Context.Var l, (term_to_var n1, Term.app hyp [ b ]))
                  , (term_to_var n2, Term.app hyp [ a2 ]) ))
               p4
               (Term.app conc [ c2 ])
           ; atm
               (Context.Ctx (Context.Var l, (term_to_var n1, Term.app hyp [ b ])))
               p5
               (Term.app conc [ a2 ])
           ]
         in
         let schema =
           [ Context.B ([ "A", ity ], [ term_to_var x, Term.app hyp [ a1 ] ]) ]
         in
         (* let f_res = *)
         (*   try *)
         (*     apply [("c",schema)] seq f args *)
         (*   with *)
         (*   | Unify.UnifyFailure e -> (print_endline (Unify.explain_failure e); *)
         (*                              raise (Unify.UnifyFailure e)) *)
         (* in *)
         (* assert_pprint_equal *)
         (*   "exists P3, {L, n2:hyp B |- P3 : conc C}" *)
         (*   f_res) ; *)
         let f_res =
           try
             let vwiths = [ "A", a2; "C", c2; "P1", p4; "P2", p5 ] in
             let cwiths =
               [ "E", Context.Ctx (Context.Var l, (term_to_var n1, Term.app hyp [ b ])) ]
             in
             apply_with [ "c", schema ] seq f args (vwiths, cwiths)
           with
           | Unify.UnifyFailure e ->
             print_endline (Unify.explain_failure e);
             raise (Unify.UnifyFailure e)
         in
         assert_pprint_equal "exists P3, {L, n1:hyp B |- P3 : conc C}" f_res)
       ; ("Cannot instantiate ctx var multiple times"
         >:: fun () ->
         let seq = Sequent.make_sequent_from_goal ~form:Bottom () in
         let g = Context.ctx_var "G" in
         let g1 = Context.ctx_var "G1" in
         let g2 = Context.ctx_var "G2" in
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let e3 = var Eigen "E3" 0 ity in
         let e4 = var Eigen "E4" 0 ity in
         let e5 = var Eigen "E5" 0 ity in
         List.iter
           (fun v -> Term.term_to_pair v |> Sequent.add_var seq)
           [ e1; e2; e3; e4; e5 ];
         List.iter
           (fun g -> Sequent.add_ctxvar seq g (Context.CtxTy ("c", [])))
           [ g; g1; g2 ];
         let f =
           ctx
             [ "G", "c" ]
             (forall
                [ "E1", ity; "E2", ity ]
                (imp
                   (atm (Context.Var g) e1 tm)
                   (imp
                      (atm (Context.Var g) e2 tm)
                      (Formula.exists [ "E3", ity ] (atm (Context.Var g) e3 tm)))))
         in
         let args = [ atm (Context.Var g1) e4 tm; atm (Context.Var g2) e5 tm ] in
         let schemas = List.map (fun v -> v, []) [ g; g1; g2 ] in
         assert_raises (Unify.UnifyFailure Unify.Generic) (fun () ->
           Tactics.apply schemas seq f args))
       ; ("Is able to instantiate ctx var with repetitions of schema"
         >:: fun () ->
         let seq = Sequent.make_sequent_from_goal ~form:Bottom () in
         let x = const "x" ity in
         let n = nominal_var "n" ity in
         let g = Context.ctx_var "G" in
         let g1 = Context.ctx_var "G1" in
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let e3 = var Eigen "E3" 0 ity in
         List.iter (fun v -> Term.term_to_pair v |> Sequent.add_var seq) [ e3; n ];
         List.iter (fun g -> Sequent.add_ctxvar seq g (Context.CtxTy ("c", []))) [ g1 ];
         let f =
           ctx
             [ "G", "c" ]
             (forall
                [ "E1", ity ]
                (imp
                   (atm (Context.Var g) e1 tm)
                   (Formula.exists [ "E2", ity ] (atm (Context.Var g) e2 tm))))
         in
         let args = [ atm (Context.Ctx (Context.Var g1, (term_to_var n, tm))) e3 tm ] in
         let schemas = [ "c", [ Context.B ([], [ term_to_var x, tm ]) ] ] in
         assert_formula_equal
           (Formula.exists
              [ "E2", ity ]
              (atm (Context.Ctx (Context.Var g1, (term_to_var n, tm))) e2 tm))
           (Tactics.apply schemas seq f args))
       ; ("Does not instantiate context multiple times"
         >:: fun () ->
         let seq = Sequent.make_sequent_from_goal ~form:Bottom () in
         let g = Context.ctx_var "G" in
         let g1 = Context.ctx_var "G1" in
         let g2 = Context.ctx_var "G2" in
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let e3 = var Eigen "E3" 0 ity in
         let u1 = var Eigen "U1" 0 ity in
         let u2 = var Eigen "U2" 0 ity in
         List.iter (fun v -> Term.term_to_pair v |> Sequent.add_var seq) [ u1; u2 ];
         List.iter
           (fun g -> Sequent.add_ctxvar seq g (Context.CtxTy ("c", [])))
           [ g1; g2 ];
         let f =
           ctx
             [ "G", "c" ]
             (forall
                [ "E1", ity; "E2", ity ]
                (imp
                   (atm (Context.Var g) e1 tm)
                   (imp
                      (atm (Context.Var g) e2 tm)
                      (Formula.exists [ "E3", ity ] (atm (Context.Var g) e3 tm)))))
         in
         let args = [ atm (Context.Var g1) u1 tm; atm (Context.Var g2) u2 tm ] in
         let args = List.map (fun f -> Formula.norm f) args in
         let schemas = [ "c", [] ] in
         assert_raises (Unify.UnifyFailure Unify.Generic) (fun () ->
           Tactics.apply schemas seq f args))
       ; ("Matches abstractions in antecedent"
         >:: fun () ->
         let seq = Sequent.make_sequent_from_goal ~form:Bottom () in
         let x = const "x" ity in
         let y = const "y" ity in
         let g = Context.ctx_var "G" in
         let g1 = Context.ctx_var "G1" in
         let e1 = var Eigen "E1" 0 iity in
         let e2 = var Eigen "E2" 0 ity in
         let u1 = var Eigen "U1" 0 iity in
         List.iter (fun v -> Term.term_to_pair v |> Sequent.add_var seq) [ u1 ];
         List.iter (fun g -> Sequent.add_ctxvar seq g (Context.CtxTy ("c", []))) [ g1 ];
         let f =
           ctx
             [ "G", "c" ]
             (forall
                [ "E1", iity ]
                (imp
                   (atm
                      (Context.Var g)
                      (abstract "x" ity (Term.app e1 [ x ]))
                      (pi [ term_to_var x, tm ] tm))
                   (Formula.exists [ "E2", ity ] (atm (Context.Var g) e2 tm))))
         in
         let args =
           [ atm
               (Context.Var g1)
               (abstract "y" ity (Term.app u1 [ y ]))
               (pi [ term_to_var y, tm ] tm)
           ]
         in
         let args = List.map (fun f -> Sequent.norm_atom seq f) args in
         let schemas = [ "c", [] ] in
         assert_equal
           (Formula.exists [ "E2", ity ] (atm (Context.Var g1) e2 tm))
           (Tactics.apply schemas seq f args))
       ; ("Allows antecedent to have less nominals than argument"
         >:: fun () ->
         let seq = Sequent.make_sequent_from_goal ~form:Bottom () in
         let z = const "z" ity in
         let x = const "x" ity in
         let y = const "y" ity in
         let n = nominal_var "n" ity in
         let g = Context.ctx_var "G" in
         let g1 = Context.ctx_var "G1" in
         let e2 = var Eigen "E2" 0 ity in
         let u1 = var Eigen "U1" 0 iity in
         List.iter (fun v -> Term.term_to_pair v |> Sequent.add_var seq) [ u1 ];
         List.iter (fun g -> Sequent.add_ctxvar seq g (Context.CtxTy ("c", []))) [ g1 ];
         let f =
           ctx
             [ "G", "c" ]
             (imp
                (atm (Context.Var g) z tm)
                (Formula.exists [ "E2", ity ] (atm (Context.Var g) e2 tm)))
         in
         let args =
           [ atm (Context.Var g1) (abstract "y" ity z) (pi [ term_to_var y, tm ] tm) ]
         in
         let args = List.map (fun f -> Sequent.norm_atom seq f) args in
         let schemas = [ "c", [ Context.B ([], [ term_to_var x, tm ]) ] ] in
         assert_equal
           (Formula.exists
              [ "E2", ity ]
              (atm (Context.Ctx (Context.Var g1, (term_to_var n, tm))) e2 tm))
           (Tactics.apply schemas seq f args))
       ]
;;

let exists_tests =
  "Exists"
  >::: [ ("Exists test"
         >:: fun () ->
         let hyp = const "hyp" iity in
         let t = const "t" ity in
         let a = var Logic "A" 0 ity in
         let p = var Logic "P" 0 ity in
         let f = Formula.exists [ "A", ity ] (atm Context.Nil p (Term.app hyp [ a ])) in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         exists seq t;
         assert_pprint_equal "{P : hyp t}" seq.goal)
       ; ("Exists fail test"
         >:: fun () ->
         let hyp = const "hyp" iity in
         let t = const "t" iity in
         let a = var Logic "A" 0 ity in
         let p = var Logic "P" 0 ity in
         let f = Formula.exists [ "A", ity ] (atm Context.Nil p (Term.app hyp [ a ])) in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         assert_raises (Tactics.InvalidTerm t) (fun () -> exists seq t))
       ]
;;

let extract_tests =
  "Extract Types"
  >::: [ ("Able to extract typing information from signature"
         >:: fun () ->
         let d = var Eigen "D" 0 ity in
         let t = var Eigen "T" 0 ity in
         let e = var Eigen "E" 0 ity in
         let f = atm Context.Nil d (Term.app typeof [ e; t ]) in
         let expected_form = atm Context.Nil t ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_var seq (term_to_pair d);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         extract_ty_info eval_sig seq 5 [ f ]
         |> List.mem expected_form
         |> assert_bool "Not able to extract type")
       ; ("Extracted types do not weaken into a ctx"
         >:: fun () ->
         let d = var Eigen "D" 0 ity in
         let t = var Eigen "T" 0 ity in
         let e = var Eigen "E" 0 ity in
         let n1 = var Nominal "n1" 3 ity in
         let f = atm Context.Nil d (Term.app typeof [ e; t ]) in
         let expected_form = atm (Context.Ctx (Context.Nil, (term_to_var n1, tm))) t ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_var seq (term_to_pair d);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         extract_ty_info eval_sig seq 5 [ f ]
         |> List.mem expected_form
         |> not
         |> assert_bool "Extraction weakens into contexts")
       ; ("Extracted types do not strengthen out of a ctx"
         >:: fun () ->
         let d = var Eigen "D" 0 ity in
         let t = var Eigen "T" 0 ity in
         let e = var Eigen "E" 0 ity in
         let n1 = var Nominal "n1" 3 ity in
         let g = Context.Ctx (Context.Nil, (term_to_var n1, tm)) in
         let f = atm g d (Term.app typeof [ e; t ]) in
         let expected_form = atm Context.Nil t ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_var seq (term_to_pair d);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         extract_ty_info eval_sig seq 5 [ f ]
         |> List.mem expected_form
         |> not
         |> assert_bool "Extraction strengthens into contexts")
       ; ("Doesn't extract types from type when depth set to 0"
         >:: fun () ->
         let d = var Eigen "D" 0 ity in
         let t = var Eigen "T" 0 ity in
         let e = var Eigen "E" 0 ity in
         let f = atm Context.Nil d (Term.app typeof [ e; t ]) in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_var seq (term_to_pair d);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         extract_ty_info eval_sig seq 0 [ f ]
         |> List.equal Formula.eq [ f ]
         |> assert_bool "Performs extraction when depth is 0")
       ; ("Doesn't extract types from term when depth is 0"
         >:: fun () ->
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let f = atm Context.Nil (Term.app Test_helper.app [ e1; e2 ]) tm in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2 ];
         extract_ty_info eval_sig seq 0 [ f ]
         |> List.equal Formula.eq [ f ]
         |> assert_bool "Performs extraction when depth is 0")
       ; ("Extracts types from terms one deep from sig"
         >:: fun () ->
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let f = atm Context.Nil (Term.app Test_helper.app [ e1; e2 ]) tm in
         let expected_form = atm Context.Nil e1 tm in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2 ];
         extract_ty_info eval_sig seq 5 [ f ]
         |> List.mem expected_form
         |> assert_bool "Extraction doesn't work on terms at depth 1")
       ; ("Extracts types from terms multiple deep from sig"
         >:: fun () ->
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let e3 = var Eigen "E3" 0 ity in
         let f =
           atm
             Context.Nil
             (Term.app Test_helper.app [ e3; Term.app Test_helper.app [ e1; e2 ] ])
             tm
         in
         let expected_form = atm Context.Nil e1 tm in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2; e3 ];
         extract_ty_info eval_sig seq 5 [ f ]
         |> List.mem expected_form
         |> assert_bool "Extraction doesn't work on terms at depth greater than 1")
       ; ("Extracting types returns only unique formulas"
         >:: fun () ->
         let e = var Eigen "E" 0 ity in
         let f = atm Context.Nil e ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_var seq (term_to_pair e);
         extract_ty_info eval_sig seq 5 [ f; f ]
         |> List.equal Formula.eq [ f ]
         |> assert_bool "Returns duplicate formulas")
       ; ("Extraction alternates between terms and types - starting with types"
         >:: fun () ->
         (* Given a new type declaration [foo: tm -> Type]
            and formula {D: foo (app e1 e2)}, the type extraction
            should firstly give {app e1 e2 : tm} then term extraction
            should give {e1: tm}. Will fail if term-type extraction doesn't
            alternate properly *)
         let foo = const "foo" iity in
         let new_ty =
           Signature.ty_dec
             "foo"
             (Term.pi [ term_to_var (const ~ts:2 "e" ity), tm ] Term.Type)
             0
             (Signature.Prefix 0)
             []
         in
         let signature = Signature.add_type_decl eval_sig new_ty in
         let e1 = var Eigen "e1" 0 ity in
         let e2 = var Eigen "e2" 0 ity in
         let a = Term.app Test_helper.app [ e1; e2 ] in
         let d = var Eigen "D" 0 ity in
         let f = atm Context.Nil d (Term.app foo [ a ]) in
         let expected_form = atm Context.Nil e1 tm in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2; d ];
         extract_ty_info signature seq 5 [ f ]
         |> List.mem expected_form
         |> assert_bool "Does not extract multiple deep")
       ; ("Extraction raises success when it finds something not well formed"
         >:: fun () ->
         (* Given a new type declaration [foo: tm -> Type]
            an obj [bar : tm -> foo -> tm]
            and formula {bar (app e1 e2) (foo (app e1 e2)) : tm}, the type extraction
            will find that foo is not in the signature as an object. This indicates
            that it's not a well formed atomic term and as such the proof is vacuously true
          *)
         let foo = const "foo" iity in
         let new_ty =
           Signature.ty_dec
             "foo"
             (Term.pi [ term_to_var (const ~ts:2 "e" ity), tm ] Term.Type)
             0
             (Signature.Prefix 0)
             []
         in
         let bar = const "bar" iiity in
         let signature = Signature.add_type_decl eval_sig new_ty in
         let new_obj =
           let x = const ~ts:2 "x" ity in
           Signature.obj_dec
             "bar"
             (Term.pi
                [ term_to_var x, tm
                ; term_to_var (const ~ts:2 "y" ity), Term.app foo [ x ]
                ]
                tm)
             0
             (Signature.Prefix 0)
         in
         let signature = Signature.add_obj_decl signature new_obj in
         let e1 = var Eigen "e1" 0 ity in
         let e2 = var Eigen "e2" 0 ity in
         let a = Term.app Test_helper.app [ e1; e2 ] in
         let b = Term.app foo [ a ] in
         let f = atm Context.Nil (Term.app bar [ a; b ]) tm in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2 ];
         assert_raises Tactics.Success (fun () -> extract_ty_info signature seq 5 [ f ]))
       ; ("Extraction substitutes for dependent types correctly"
         (* Given a new type declaration [foo: tm -> Type]
            an obj [bar : pi x: tm . pi y: foo x . tm]
            and formula {bar (app e1 e2) D : tm}, the type extraction will need to determine
            that D is of type (foo x) and correctly substitute x for (app e1 e2) to give
            a new judgement of the form {D: foo (app e1 e2)}
          *)
         >:: fun () ->
         let foo = const "foo" iity in
         let new_ty =
           Signature.ty_dec
             "foo"
             (Term.pi [ term_to_var (const ~ts:2 "e" ity), tm ] Term.Type)
             0
             (Signature.Prefix 0)
             []
         in
         let bar = const "bar" iiity in
         let d = var Eigen "D" 0 ity in
         let signature = Signature.add_type_decl eval_sig new_ty in
         let new_obj =
           let x = const ~ts:2 "x" ity in
           Signature.obj_dec
             "bar"
             (Term.pi
                [ term_to_var x, tm
                ; term_to_var (const ~ts:2 "y" ity), Term.app foo [ x ]
                ]
                tm)
             0
             (Signature.Prefix 0)
         in
         let signature = Signature.add_obj_decl signature new_obj in
         let e1 = var Eigen "e1" 0 ity in
         let e2 = var Eigen "e2" 0 ity in
         let a = Term.app Test_helper.app [ e1; e2 ] in
         let f = atm Context.Nil (Term.app bar [ a; d ]) tm in
         let expected = atm Context.Nil d (Term.app foo [ a ]) in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2 ];
         extract_ty_info signature seq 5 [ f ]
         |> List.mem expected
         |> assert_bool "Doesn't substitute dependencies in types")
       ]
;;

let assert_search_success search_func = assert_raises Tactics.Success search_func
let assert_search_fail search_func = assert_equal () (search_func ())

let search_tests =
  "Search"
  >::: [ (* True is not an atomic formula. *)
         (* "True is derivable" >:: *)
         (*   (fun () -> *)
         (*     let seq = Sequent.make_sequent_from_goal Formula.Top in *)
         (*     assert_raises Tactics.Success (fun () -> search eval_sig seq)) ; *)
         ("Should check hypotheses"
         >:: fun () ->
         let x = var Eigen "X" 0 ity in
         let f = atm Context.Nil x tm in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_hyp seq ~name:"H1" f;
         assert_raises Tactics.Success (fun () -> search ~depth:5 eval_sig seq))
       ; ("Should apply LF proof steps"
         >:: fun () ->
         let x = const "x" ity in
         let y = const "y" ity in
         let f =
           atm
             Context.Nil
             (abstract "x" ity (abstract "y" ity (Term.app arrow [ x; y ])))
             (Term.pi [ term_to_var x, ty; term_to_var y, ty ] ty)
         in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         assert_raises Tactics.Success (fun () -> search ~depth:5 eval_sig seq))
       ; ("Should permute nominal constants"
         >:: fun () ->
         let n1 = var Nominal "n1" 3 ity in
         let n2 = var Nominal "n2" 3 ity in
         let seq = Sequent.make_sequent_from_goal ~form:(atm Context.Nil n1 tm) () in
         Sequent.add_var seq (term_to_pair n1);
         Sequent.add_var seq (term_to_pair n2);
         Sequent.add_hyp seq ~name:"H1" (atm Context.Nil n2 tm);
         assert_raises Tactics.Success (fun () -> search ~depth:5 eval_sig seq))
       ; ("Permutation of nominals in context"
         >:: fun () ->
         let n1 = var Nominal "n1" 3 ity in
         let n2 = var Nominal "n2" 3 ity in
         let x = var Eigen "X" 1 ity in
         let f = atm (Context.Ctx (Context.Nil, (term_to_var n1, tm))) x ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         let hyp = atm (Context.Ctx (Context.Nil, (term_to_var n2, tm))) x ty in
         Sequent.add_var seq (term_to_pair n1);
         Sequent.add_var seq (term_to_pair n2);
         Sequent.add_var seq (term_to_pair x);
         Sequent.add_hyp seq ~name:"H1" hyp;
         assert_raises Tactics.Success (fun () -> search ~depth:5 eval_sig seq))
       ; ("Able to extract typing information from signature"
         >:: fun () ->
         let d = var Eigen "D" 0 ity in
         let t = var Eigen "T" 0 ity in
         let e = var Eigen "E" 0 ity in
         let f = atm Context.Nil t ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_var seq (term_to_pair d);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         Sequent.add_hyp seq ~name:"H1" (atm Context.Nil d (Term.app typeof [ e; t ]));
         assert_search_success (fun () -> search ~depth:5 eval_sig seq))
       ; ("Extracted types do not weaken into a ctx"
         >:: fun () ->
         let d = var Eigen "D" 0 ity in
         let t = var Eigen "T" 0 ity in
         let e = var Eigen "E" 0 ity in
         let n1 = var Nominal "n1" 3 ity in
         let f = atm (Context.Ctx (Context.Nil, (term_to_var n1, tm))) t ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_var seq (term_to_pair d);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         Sequent.add_hyp seq ~name:"H1" (atm Context.Nil d (Term.app typeof [ e; t ]));
         assert_search_fail (fun () -> search ~depth:5 eval_sig seq))
       ; ("Extracted types do not strengthen out of a ctx"
         >:: fun () ->
         let d = var Eigen "D" 0 ity in
         let t = var Eigen "T" 0 ity in
         let e = var Eigen "E" 0 ity in
         let n1 = var Nominal "n1" 3 ity in
         let f = atm Context.Nil t ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         let g = Context.Ctx (Context.Nil, (term_to_var n1, tm)) in
         Sequent.add_var seq (term_to_pair d);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         Sequent.add_hyp seq ~name:"H1" (atm g d (Term.app typeof [ e; t ]));
         assert_search_fail (fun () -> search ~depth:5 eval_sig seq))
       ; ("Doesn't extract types when depth set to 0"
         >:: fun () ->
         let d = var Eigen "D" 0 ity in
         let t = var Eigen "T" 0 ity in
         let e = var Eigen "E" 0 ity in
         let f = atm Context.Nil t ty in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         Sequent.add_var seq (term_to_pair d);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         Sequent.add_hyp seq ~name:"H1" (atm Context.Nil d (Term.app typeof [ e; t ]));
         assert_search_fail (fun () -> search ~depth:0 eval_sig seq))
       ; ("Extracts types from terms one deep from sig"
         >:: fun () ->
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let f = atm Context.Nil e1 tm in
         let h1 = atm Context.Nil (Term.app Test_helper.app [ e1; e2 ]) tm in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2 ];
         Sequent.add_hyp seq ~name:"H1" h1;
         assert_search_success (fun () -> search ~depth:5 eval_sig seq))
       ; ("Extracts types from terms multiple deep from sig"
         >:: fun () ->
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let e3 = var Eigen "E3" 0 ity in
         let f = atm Context.Nil e1 tm in
         let h1 =
           atm
             Context.Nil
             (Term.app Test_helper.app [ e3; Term.app Test_helper.app [ e1; e2 ] ])
             tm
         in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2; e3 ];
         Sequent.add_hyp seq ~name:"H1" h1;
         assert_search_success (fun () -> search ~depth:5 eval_sig seq))
       ; ("Doesn't extract types when depth is 0"
         >:: fun () ->
         let e1 = var Eigen "E1" 0 ity in
         let e2 = var Eigen "E2" 0 ity in
         let f = atm Context.Nil e1 tm in
         let h1 = atm Context.Nil (Term.app Test_helper.app [ e1; e2 ]) tm in
         let seq = Sequent.make_sequent_from_goal ~form:f () in
         List.iter (fun x -> term_to_pair x |> Sequent.add_var seq) [ e1; e2 ];
         Sequent.add_hyp seq ~name:"H1" h1;
         assert_search_fail (fun () -> search ~depth:0 eval_sig seq))
       ]
;;

let inst_tests =
  "Inst"
  >::: [ ("Simple instantiation test"
         >:: fun () ->
         (* instantiate an assumption {n:tm |- n: tm} with term (app t t) 
             with { |- t :tm} in assumptions. *)
         let n = var Nominal "n" 3 ity in
         let t = var Eigen "T" 1 ity in
         let f1 = atm Context.Nil t tm in
         let f2 = atm (Context.Ctx (Context.Nil, (term_to_var n, tm))) n tm in
         let seq = Sequent.make_sequent_from_goal ~form:Top () in
         Sequent.add_var seq (term_to_pair n);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_hyp seq ~name:"H1" f1;
         Sequent.add_hyp seq ~name:"H2" f2;
         assert_pprint_equal "{T : tm}" (inst ~depth:5 eval_sig seq f2 [ "n", t ]))
       ; ("Instantiation in context and types"
         >:: fun () ->
         let n1 = var Nominal "n1" 3 ity in
         let n2 = var Nominal "n2" 3 ity in
         let t = var Eigen "T" 1 ity in
         let e = var Eigen "E" 1 ity in
         let f1 = atm Context.Nil t tm in
         let g =
           Context.Ctx
             ( Context.Ctx (Context.Nil, (term_to_var n1, tm))
             , (term_to_var n2, Term.app arrow [ t; n1 ]) )
         in
         let f2 = atm g e (Term.app eval [ n1; t ]) in
         let seq = Sequent.make_sequent_from_goal ~form:Top () in
         Sequent.add_var seq (term_to_pair n1);
         Sequent.add_var seq (term_to_pair n2);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_var seq (term_to_pair e);
         Sequent.add_hyp seq ~name:"H1" f1;
         Sequent.add_hyp seq ~name:"H2" f2;
         assert_pprint_equal
           "{n2:arrow T T |- E : eval T T}"
           (inst ~depth:5 eval_sig seq f2 [ "n1", t ]))
       ; ("Extraction from type to term works" >:: fun () -> ())
       ; ("Instantiation must be of the right LF type"
         >:: fun () ->
         let n = var Nominal "n" 3 ity in
         let t = var Eigen "T" 1 ity in
         let f1 = atm Context.Nil t ty in
         let f2 = atm (Context.Ctx (Context.Nil, (term_to_var n, tm))) n tm in
         let seq = Sequent.make_sequent_from_goal ~form:Top () in
         Sequent.add_var seq (term_to_pair n);
         Sequent.add_var seq (term_to_pair t);
         Sequent.add_hyp seq ~name:"H1" f1;
         Sequent.add_hyp seq ~name:"H2" f2;
         assert_raises
           (Tactics.InstTypeError (atm Context.Nil t tm))
           (fun () -> inst ~depth:5 eval_sig seq f2 [ "n", t ]))
       ]
;;

let tests =
  "Tactics"
  >::: [ case_tests; apply_tests; exists_tests; extract_tests; search_tests; inst_tests ]
;;
