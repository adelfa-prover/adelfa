  $ adelfa -i double-spec.ath
  Welcome!
  >> Specification "stlc.lf".
  
  >> Specification "stlc.lf".
  Error: Specification file already given. Not reading `stlc.lf'
  [1]

  $ adelfa -i abort.ath
  Welcome!
  >> Specification "stlc.lf".
  
  >> Schema f := {}(y:tm).
  
  >> Theorem abort-test: forall  X, {X : tm} => false.
  
  Subgoal abort-test:
  
  
  ==================================
  forall X, {X : tm} => False
  
  abort-test>> intros.
  
  Subgoal abort-test:
  
  Vars: X:o
  H1:{X : tm}
  
  ==================================
  False
  
  abort-test>> cases H1.
  
  Subgoal abort-test.1:
  
  
  ==================================
  False
  
  Subgoal abort-test.2 is:
   False
  
  Subgoal abort-test.3 is:
   False
  
  abort-test.1>> abort.
  Proof Aborted.
  
  >> undo.
  
  >> Theorem undid-schema: ctx  G:f, forall  X, {X : tm} => false.
  Typing error: file abort.ath, line 16, characters 27-30.
  can't find context schema f.
  [1]

  $ adelfa -i undo-complete.ath
  Welcome!
  >> Specification "stlc.lf".
  
  >> Theorem undo-complete-formula: forall  X, {X : tm} => exists  E, {E : tm}.
  
  Subgoal undo-complete-formula:
  
  
  ==================================
  forall X, {X : tm} => exists E, {E : tm}
  
  undo-complete-formula>> intros.
  
  Subgoal undo-complete-formula:
  
  Vars: X:o
  H1:{X : tm}
  
  ==================================
  exists E, {E : tm}
  
  undo-complete-formula>> exists empty.
  
  Subgoal undo-complete-formula:
  
  Vars: X:o
  H1:{X : tm}
  
  ==================================
  {empty : tm}
  
  undo-complete-formula>> search.
  Proof Completed!
  
  >> undo.
  
  Subgoal undo-complete-formula:
  
  Vars: X:o
  H1:{X : tm}
  
  ==================================
  {empty : tm}
  
  undo-complete-formula>> search.
  Proof Completed!
  
  >> Goodbye!

  $ adelfa -i undo-toplevel.ath
  Welcome!
  >> Specification "stlc.lf".
  
  >> Schema c := {}(x:tm).
  
  >> undo.
  
  >> Theorem undid-schema: ctx  G:c, forall  X, {X : tm} => false.
  Typing error: file undo-toplevel.ath, line 8, characters 27-30.
  can't find context schema c.
  [1]
