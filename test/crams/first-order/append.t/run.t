  $ adelfa -i append.ath
  Welcome!
  >> Specification "append.lf".
  
  >> Theorem app-nil: forall  L, {L : list} => exists  D, {D : append L nil L}.
  
  Subgoal app-nil:
  
  
  ==================================
  forall L, {L : list} => exists D, {D : append L nil L}
  
  app-nil>> induction on 1.
  
  Subgoal app-nil:
  
  IH:forall L, {L : list}* => exists D, {D : append L nil L}
  
  ==================================
  forall L, {L : list}@ => exists D, {D : append L nil L}
  
  app-nil>> intros.
  
  Subgoal app-nil:
  
  Vars: L:o
  IH:forall L, {L : list}* => exists D, {D : append L nil L}
  H1:{L : list}@
  
  ==================================
  exists D, {D : append L nil L}
  
  app-nil>> cases H1.
  
  Subgoal app-nil.1:
  
  Vars: N:o, L1:o
  IH:forall L, {L : list}* => exists D, {D : append L nil L}
  H2:{N : nat}*
  H3:{L1 : list}*
  
  ==================================
  exists D, {D : append (cons N L1) nil (cons N L1)}
  
  Subgoal app-nil.2 is:
   exists D, {D : append nil nil nil}
  
  app-nil.1>> apply IH to H3.
  
  Subgoal app-nil.1:
  
  Vars: D:o, N:o, L1:o
  IH:forall L, {L : list}* => exists D, {D : append L nil L}
  H2:{N : nat}*
  H3:{L1 : list}*
  H4:{D : append L1 nil L1}
  
  ==================================
  exists D, {D : append (cons N L1) nil (cons N L1)}
  
  Subgoal app-nil.2 is:
   exists D, {D : append nil nil nil}
  
  app-nil.1>> exists append-cons N L1 nil L1 D.
  
  Subgoal app-nil.1:
  
  Vars: D:o, N:o, L1:o
  IH:forall L, {L : list}* => exists D, {D : append L nil L}
  H2:{N : nat}*
  H3:{L1 : list}*
  H4:{D : append L1 nil L1}
  
  ==================================
  {append-cons N L1 nil L1 D : append (cons N L1) nil (cons N L1)}
  
  Subgoal app-nil.2 is:
   exists D, {D : append nil nil nil}
  
  app-nil.1>> search.
  
  Subgoal app-nil.2:
  
  IH:forall L, {L : list}* => exists D, {D : append L nil L}
  
  ==================================
  exists D, {D : append nil nil nil}
  
  app-nil.2>> exists append-nil nil.
  
  Subgoal app-nil.2:
  
  IH:forall L, {L : list}* => exists D, {D : append L nil L}
  
  ==================================
  {append-nil nil : append nil nil nil}
  
  app-nil.2>> search.
  Proof Completed!
  
  >> Goodbye!
