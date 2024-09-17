open OUnit
open Test_helper
module S = Sequent

let copy_tests =
  "Copy"
  >::: [ ("Modifying copied object doesn't modify original"
          >:: fun () ->
          let s = S.make_sequent_from_goal ~form:Bottom () in
          let s_copy = S.cp_sequent s in
          let () = s_copy.goal <- Top in
          assert_formula_equal s_copy.goal Top;
          assert_formula_equal s.goal Bottom)
       ; ("Modifying original object doesn't modify copied"
          >:: fun () ->
          let s = S.make_sequent_from_goal ~form:Bottom () in
          let s_copy = S.cp_sequent s in
          let () = s.goal <- Top in
          assert_formula_equal s.goal Top;
          assert_formula_equal s_copy.goal Bottom)
       ; ("Assigning sequent modifies only first"
          >:: fun () ->
          let s1 = S.make_sequent_from_goal ~form:Bottom () in
          let s2 = S.make_sequent_from_goal ~form:Top () in
          S.assign_sequent s1 s2;
          assert_formula_equal s1.goal s2.goal;
          assert_formula_equal s2.goal Formula.Top)
       ]
;;

let tests = "Sequent" >::: [ copy_tests ]
