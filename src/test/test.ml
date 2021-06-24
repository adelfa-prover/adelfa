open OUnit
open Test_helper
  
let tests = "tests" >:::
  [
    Etanorm_test.tests ;
    Unify_test.tests ;
    Tactics_test.tests ;
  ]

let tests = extract_tests [] tests

let _ = run_test_tt_main tests
  
