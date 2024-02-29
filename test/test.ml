open OUnit
open Test_helper

let tests =
  "tests"
  >::: [ Etanorm_test.tests
       ; Unify_test.tests
       ; Tactics_test.tests
       ; Prover_test.tests
       ; Sequent_test.tests
       ; State_test.tests
       ; Typing_test.tests
       ; Subordination_test.tests
       ; Context_test.tests
       ; Formula_test.tests
       ]
;;

let tests = extract_tests [] tests
let _ = run_test_tt_main tests
