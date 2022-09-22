  $ adelfa -i even-or-odd.ath
  Welcome!
  >> Specification even-or-odd.lf.
  
  >> Theorem even-or-odd:
      forall  N,
        {N : nat} => exists  D, {D : even N} \/ exists  D, {D : odd N}.
  
  Subgoal even-or-odd:
  
  
  ==================================
  forall N, {N : nat} => exists D, {D : even N} \/ exists D, {D : odd N}
  
  even-or-odd>> induction on 1.
  
  Subgoal even-or-odd:
  
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  
  ==================================
  forall N, {N : nat}@ => exists D, {D : even N} \/ exists D, {D : odd N}
  
  even-or-odd>> intros.
  
  Subgoal even-or-odd:
  
  Vars: N:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H1:{N : nat}@
  
  ==================================
  exists D, {D : even N} \/ exists D, {D : odd N}
  
  even-or-odd>> cases H1.
  
  Subgoal even-or-odd.1:
  
  Vars: x:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H2:{x : nat}*
  
  ==================================
  exists D, {D : even (s x)} \/ exists D, {D : odd (s x)}
  
  Subgoal even-or-odd.2 is:
   exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.1>> apply IH to H2.
  
  Subgoal even-or-odd.1:
  
  Vars: x:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H2:{x : nat}*
  H3:exists D, {D : even x} \/ exists D, {D : odd x}
  
  ==================================
  exists D, {D : even (s x)} \/ exists D, {D : odd (s x)}
  
  Subgoal even-or-odd.2 is:
   exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.1>> cases H3.
  
  Subgoal even-or-odd.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H2:{x : nat}*
  H3:{D : even x}
  
  ==================================
  exists D, {D : even (s x)} \/ exists D, {D : odd (s x)}
  
  Subgoal even-or-odd.1 is:
   exists D, {D : even (s x)} \/ exists D, {D : odd (s x)}
  
  Subgoal even-or-odd.2 is:
   exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.1>> right.
  
  Subgoal even-or-odd.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H2:{x : nat}*
  H3:{D : even x}
  
  ==================================
  exists D, {D : odd (s x)}
  
  Subgoal even-or-odd.1 is:
   exists D, {D : even (s x)} \/ exists D, {D : odd (s x)}
  
  Subgoal even-or-odd.2 is:
   exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.1>> exists odd-s x D.
  
  Subgoal even-or-odd.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H2:{x : nat}*
  H3:{D : even x}
  
  ==================================
  {odd-s x D : odd (s x)}
  
  Subgoal even-or-odd.1 is:
   exists D, {D : even (s x)} \/ exists D, {D : odd (s x)}
  
  Subgoal even-or-odd.2 is:
   exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.1>> search.
  
  Subgoal even-or-odd.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H2:{x : nat}*
  H3:{D : odd x}
  
  ==================================
  exists D, {D : even (s x)} \/ exists D, {D : odd (s x)}
  
  Subgoal even-or-odd.2 is:
   exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.1>> left.
  
  Subgoal even-or-odd.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H2:{x : nat}*
  H3:{D : odd x}
  
  ==================================
  exists D, {D : even (s x)}
  
  Subgoal even-or-odd.2 is:
   exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.1>> exists even-s x D.
  
  Subgoal even-or-odd.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  H2:{x : nat}*
  H3:{D : odd x}
  
  ==================================
  {even-s x D : even (s x)}
  
  Subgoal even-or-odd.2 is:
   exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.1>> search.
  
  Subgoal even-or-odd.2:
  
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  
  ==================================
  exists D, {D : even z} \/ exists D, {D : odd z}
  
  even-or-odd.2>> left.
  
  Subgoal even-or-odd.2:
  
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  
  ==================================
  exists D, {D : even z}
  
  even-or-odd.2>> exists even-z.
  
  Subgoal even-or-odd.2:
  
  IH:forall N, {N : nat}* => exists D, {D : even N} \/ exists D, {D : odd N}
  
  ==================================
  {even-z : even z}
  
  even-or-odd.2>> search.
  Proof Completed!
  
  >> Goodbye!
