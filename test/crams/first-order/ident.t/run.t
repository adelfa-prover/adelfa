  $ adelfa -i ident.ath
  Welcome!
  >> Specification "ident.lf".
  
  >> Theorem identity:
      exists  I,
        forall  X,
          {X : nat} => exists  D, {D : plus I X X} /\
            forall  X, {X : nat} => exists  D, {D : plus X I X}.
  
  Subgoal identity:
  
  
  ==================================
  exists I,
    forall X, {X : nat} => exists D, {D : plus I X X} /\
        forall X, {X : nat} => exists D, {D : plus X I X}
  
  identity>> exists z.
  
  Subgoal identity:
  
  
  ==================================
  forall X, {X : nat} => exists D, {D : plus z X X} /\
      forall X, {X : nat} => exists D, {D : plus X z X}
  
  identity>> split.
  
  Subgoal identity:
  
  
  ==================================
  forall X, {X : nat} => exists D, {D : plus z X X}
  
  Subgoal identity is:
   forall X, {X : nat} => exists D, {D : plus X z X}
  
  identity>> intros.
  
  Subgoal identity:
  
  Vars: X:o
  H1:{X : nat}
  
  ==================================
  exists D, {D : plus z X X}
  
  Subgoal identity is:
   forall X, {X : nat} => exists D, {D : plus X z X}
  
  identity>> exists plus_z X.
  
  Subgoal identity:
  
  Vars: X:o
  H1:{X : nat}
  
  ==================================
  {plus_z X : plus z X X}
  
  Subgoal identity is:
   forall X, {X : nat} => exists D, {D : plus X z X}
  
  identity>> search.
  
  Subgoal identity:
  
  
  ==================================
  forall X, {X : nat} => exists D, {D : plus X z X}
  
  identity>> induction on 1.
  
  Subgoal identity:
  
  IH:forall X, {X : nat}* => exists D, {D : plus X z X}
  
  ==================================
  forall X, {X : nat}@ => exists D, {D : plus X z X}
  
  identity>> intros.
  
  Subgoal identity:
  
  Vars: X:o
  IH:forall X, {X : nat}* => exists D, {D : plus X z X}
  H1:{X : nat}@
  
  ==================================
  exists D, {D : plus X z X}
  
  identity>> cases H1.
  
  Subgoal identity.1:
  
  Vars: x:o
  IH:forall X, {X : nat}* => exists D, {D : plus X z X}
  H2:{x : nat}*
  
  ==================================
  exists D, {D : plus (s x) z (s x)}
  
  Subgoal identity.2 is:
   exists D, {D : plus z z z}
  
  identity.1>> apply IH to H2.
  
  Subgoal identity.1:
  
  Vars: D:o, x:o
  IH:forall X, {X : nat}* => exists D, {D : plus X z X}
  H2:{x : nat}*
  H3:{D : plus x z x}
  
  ==================================
  exists D, {D : plus (s x) z (s x)}
  
  Subgoal identity.2 is:
   exists D, {D : plus z z z}
  
  identity.1>> exists plus_s x z x D.
  
  Subgoal identity.1:
  
  Vars: D:o, x:o
  IH:forall X, {X : nat}* => exists D, {D : plus X z X}
  H2:{x : nat}*
  H3:{D : plus x z x}
  
  ==================================
  {plus_s x z x D : plus (s x) z (s x)}
  
  Subgoal identity.2 is:
   exists D, {D : plus z z z}
  
  identity.1>> search.
  
  Subgoal identity.2:
  
  IH:forall X, {X : nat}* => exists D, {D : plus X z X}
  
  ==================================
  exists D, {D : plus z z z}
  
  identity.2>> exists plus_z z.
  
  Subgoal identity.2:
  
  IH:forall X, {X : nat}* => exists D, {D : plus X z X}
  
  ==================================
  {plus_z z : plus z z z}
  
  identity.2>> search.
  Proof Completed!
  
  >> Goodbye!
