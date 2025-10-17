  $ adelfa -i schema-transport.ath
  Welcome!
  >> Specification "schema-transport.lf".
  
  >> Schema onlyTerm := {}(x:tm).
  
  >> Theorem useless:
      ctx  G:onlyTerm,
        forall  M:o, {G |- M : tm} => exists  D:o, {G |- D : tm}.
  
  Subgoal useless:
  
  
  ==================================
  ctx G:onlyTerm, forall M, {G |- M : tm} => exists D, {G |- D : tm}
  
  useless>> intros.
  
  Subgoal useless:
  
  Vars: M:o
  Contexts: G{}:onlyTerm[]
  H1:{G |- M : tm}
  
  ==================================
  exists D, {G |- D : tm}
  
  useless>> exists M.
  
  Subgoal useless:
  
  Vars: M:o
  Contexts: G{}:onlyTerm[]
  H1:{G |- M : tm}
  
  ==================================
  {G |- M : tm}
  
  useless>> search.
  Proof Completed!
  
  >> Schema c := {T}(x:tm,y:of x T).
  
  >> Theorem uses_useless:
      ctx  G:c, forall  M:o, {G |- M : tm} => exists  D:o, {G |- D : tm}.
  
  Subgoal uses_useless:
  
  
  ==================================
  ctx G:c, forall M, {G |- M : tm} => exists D, {G |- D : tm}
  
  uses_useless>> intros.
  
  Subgoal uses_useless:
  
  Vars: M:o
  Contexts: G{}:c[]
  H1:{G |- M : tm}
  
  ==================================
  exists D, {G |- D : tm}
  
  uses_useless>> apply useless to H1.
  
  Subgoal uses_useless:
  
  Vars: D:o, M:o
  Contexts: G{}:c[]
  H1:{G |- M : tm}
  H2:{G |- D : tm}
  
  ==================================
  exists D, {G |- D : tm}
  
  uses_useless>> exists D.
  
  Subgoal uses_useless:
  
  Vars: D:o, M:o
  Contexts: G{}:c[]
  H1:{G |- M : tm}
  H2:{G |- D : tm}
  
  ==================================
  {G |- D : tm}
  
  uses_useless>> search.
  Proof Completed!
  
  >> Theorem ty_independent: ctx  G:c, forall  T:o, {G |- T : ty} => {T : ty}.
  
  Subgoal ty_independent:
  
  
  ==================================
  ctx G:c, forall T, {G |- T : ty} => {T : ty}
  
  ty_independent>> induction on 1.
  
  Subgoal ty_independent:
  
  IH:ctx G:c, forall T, {G |- T : ty}* => {T : ty}
  
  ==================================
  ctx G:c, forall T, {G |- T : ty}@ => {T : ty}
  
  ty_independent>> intros.
  
  Subgoal ty_independent:
  
  Vars: T:o
  Contexts: G{}:c[]
  IH:ctx G:c, forall T, {G |- T : ty}* => {T : ty}
  H1:{G |- T : ty}@
  
  ==================================
  {T : ty}
  
  ty_independent>> cases H1.
  
  Subgoal ty_independent:
  
  Vars: T1:o, U:o
  Contexts: G{}:c[]
  IH:ctx G:c, forall T, {G |- T : ty}* => {T : ty}
  H2:{G |- T1 : ty}*
  H3:{G |- U : ty}*
  
  ==================================
  {arr T1 U : ty}
  
  ty_independent>> apply IH to H2.
  
  Subgoal ty_independent:
  
  Vars: T1:o, U:o
  Contexts: G{}:c[]
  IH:ctx G:c, forall T, {G |- T : ty}* => {T : ty}
  H2:{G |- T1 : ty}*
  H3:{G |- U : ty}*
  H4:{T1 : ty}
  
  ==================================
  {arr T1 U : ty}
  
  ty_independent>> apply IH to H3.
  
  Subgoal ty_independent:
  
  Vars: T1:o, U:o
  Contexts: G{}:c[]
  IH:ctx G:c, forall T, {G |- T : ty}* => {T : ty}
  H2:{G |- T1 : ty}*
  H3:{G |- U : ty}*
  H4:{T1 : ty}
  H5:{U : ty}
  
  ==================================
  {arr T1 U : ty}
  
  ty_independent>> search.
  Proof Completed!
  
  >> Schema c' := {A}(a:tm,z:of a A).
  
  >> Theorem eq_independent:
      ctx  G:c', forall  T1 T2 D, {G |- D : eq T1 T2} => {D : eq T1 T2}.
  
  Subgoal eq_independent:
  
  
  ==================================
  ctx G:c',
    forall T1, forall T2, forall D, {G |- D : eq T1 T2} => {D : eq T1 T2}
  
  eq_independent>> intros.
  
  Subgoal eq_independent:
  
  Vars: D:o, T2:o, T1:o
  Contexts: G{}:c'[]
  H1:{G |- D : eq T1 T2}
  
  ==================================
  {D : eq T1 T2}
  
  eq_independent>> cases H1.
  
  Subgoal eq_independent:
  
  Vars: T2:o
  Contexts: G{}:c'[]
  H2:{G |- T2 : ty}
  
  ==================================
  {refl T2 : eq T2 T2}
  
  eq_independent>> apply ty_independent to H2.
  
  Subgoal eq_independent:
  
  Vars: T2:o
  Contexts: G{}:c'[]
  H2:{G |- T2 : ty}
  H3:{T2 : ty}
  
  ==================================
  {refl T2 : eq T2 T2}
  
  eq_independent>> abort.
  Proof Aborted.
  
  >> Schema c'' := {T}(x:tm,y:of x T,z:tm).
  
  >> Theorem eq_independent:
      ctx  G:c'', forall  T1 T2 D, {G |- D : eq T1 T2} => {D : eq T1 T2}.
  
  Subgoal eq_independent:
  
  
  ==================================
  ctx G:c'',
    forall T1, forall T2, forall D, {G |- D : eq T1 T2} => {D : eq T1 T2}
  
  eq_independent>> intros.
  
  Subgoal eq_independent:
  
  Vars: D:o, T2:o, T1:o
  Contexts: G{}:c''[]
  H1:{G |- D : eq T1 T2}
  
  ==================================
  {D : eq T1 T2}
  
  eq_independent>> cases H1.
  
  Subgoal eq_independent:
  
  Vars: T2:o
  Contexts: G{}:c''[]
  H2:{G |- T2 : ty}
  
  ==================================
  {refl T2 : eq T2 T2}
  
  eq_independent>> apply ty_independent to H2.
  Error: Failed while matching formula: {G |- T2 : ty}
  [1]
