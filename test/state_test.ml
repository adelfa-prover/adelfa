open OUnit
open Test_helper

let make_tests =
  "Make"
  >::: [ ("Make returns original object"
         >:: fun () ->
         let s : Sequent.sequent =
           { vars = []
           ; ctxvars = []
           ; hyps = []
           ; goal = Formula.Top
           ; count = 0
           ; name = "dummy"
           ; next_subgoal_id = 1
           }
         in
         let s_state =
           State.make ~copy:Sequent.cp_sequent ~assign:Sequent.assign_sequent s
         in
         assert_equal ~cmp:Sequent.eq s s_state)
       ]
;;

let undo_tests =
  "Undo"
  >::: [ ("Undoes action"
         >:: fun () ->
         let i = State.rref 1 in
         State.Undo.push ();
         i := 5;
         State.Undo.undo ();
         assert_equal !i 1)
       ; ("Can go back multiple"
         >:: fun () ->
         let i = State.rref 1 in
         State.Undo.push ();
         i := 5;
         State.Undo.push ();
         i := 10;
         State.Undo.undo ();
         assert_equal !i 5;
         State.Undo.undo ();
         assert_equal !i 1)
       ]
;;

let reload_tests =
  "Reload"
  >::: [ ("Restores old state"
         >:: fun () ->
         let s =
           State.make
             ~copy:Sequent.cp_sequent
             ~assign:Sequent.assign_sequent
             { vars = []
             ; ctxvars = []
             ; hyps = []
             ; goal = Formula.Top
             ; count = 0
             ; name = "dummy"
             ; next_subgoal_id = 1
             }
         in
         let old = State.snapshot () in
         s.name <- "New name";
         s.goal <- Bottom;
         assert_equal s.name "New name";
         assert_equal ~cmp:Formula.eq s.goal Formula.Bottom;
         State.reload old;
         assert_equal s.name "dummy";
         assert_equal ~cmp:Formula.eq s.goal Formula.Top)
       ; ("Maintains undo history"
         >:: fun () ->
         let i = State.rref 1 in
         State.Undo.push ();
         i := 5;
         let two_left = State.snapshot () in
         State.Undo.push ();
         i := 10;
         State.reload two_left;
         assert_int_equal ~msg:"Restores state" !i 5;
         State.Undo.undo ();
         assert_int_equal ~msg:"Undo stack is not restored" !i 5)
       ; ("Reloads all states tracked"
         >:: fun () ->
         let i = State.rref 1 in
         let j = State.rref 2 in
         let b = State.snapshot () in
         i := 5;
         j := 10;
         State.reload b;
         assert_int_equal !i 1;
         assert_int_equal !j 2)
       ]
;;

let tests = "State" >::: [ make_tests; undo_tests; reload_tests ]
