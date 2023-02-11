  $ adelfa -i unique.ath
  Welcome!
  >> Specification unique.lf.
  
  >> Schema c := {T}(x:tm,y:of x T).
  
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
  
  >> Theorem eq_independent:
      ctx  G:c, forall  T1 T2 D, {G |- D : eq T1 T2} => {D : eq T1 T2}.
  
  Subgoal eq_independent:
  
  
  ==================================
  ctx G:c,
    forall T1, forall T2, forall D, {G |- D : eq T1 T2} => {D : eq T1 T2}
  
  eq_independent>> intros.
  
  Subgoal eq_independent:
  
  Vars: D:o, T2:o, T1:o
  Contexts: G{}:c[]
  H1:{G |- D : eq T1 T2}
  
  ==================================
  {D : eq T1 T2}
  
  eq_independent>> cases H1.
  
  Subgoal eq_independent:
  
  Vars: T2:o
  Contexts: G{}:c[]
  H2:{G |- T2 : ty}
  
  ==================================
  {refl T2 : eq T2 T2}
  
  eq_independent>> apply ty_independent to H2.
  
  Subgoal eq_independent:
  
  Vars: T2:o
  Contexts: G{}:c[]
  H2:{G |- T2 : ty}
  H3:{T2 : ty}
  
  ==================================
  {refl T2 : eq T2 T2}
  
  eq_independent>> search.
  Proof Completed!
  
  >> Theorem ty_unique_aux:
      ctx  G:c,
        forall  E T1 T2 D1 D2,
          {G |- D1 : of E T1} =>
            {G |- D2 : of E T2} => exists  D3, {G |- D3 : eq T1 T2}.
  
  Subgoal ty_unique_aux:
  
  
  ==================================
  ctx G:c,
    forall E, forall T1, forall T2, forall D1, forall D2,
      {G |- D1 : of E T1} =>
          {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  
  ty_unique_aux>> induction on 1.
  
  Subgoal ty_unique_aux:
  
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  
  ==================================
  ctx G:c,
    forall E, forall T1, forall T2, forall D1, forall D2,
      {G |- D1 : of E T1}@ =>
          {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  
  ty_unique_aux>> intros.
  
  Subgoal ty_unique_aux:
  
  Vars: D2:o, D1:o, T2:o, T1:o, E:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- D1 : of E T1}@
  H2:{G |- D2 : of E T2}
  
  ==================================
  exists D3, {G |- D3 : eq T1 T2}
  
  ty_unique_aux>> cases H1.
  
  Subgoal ty_unique_aux.1:
  
  Vars: a1:(o) -> (o) -> o, R:(o) -> o, T3:o, T4:o, D2:o, T2:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:
      {G |- of_abs T3 T4 ([c13]R c13) ([c14][c15]a1 c14 c15) :
        of (abs T3 ([c4]R c4)) (arr T3 T4)}@
  H2:{G |- D2 : of (abs T3 ([c4]R c4)) T2}
  H3:{G |- T3 : ty}*
  H4:{G |- T4 : ty}*
  H5:{G, n:tm |- R n : tm}*
  H6:{G, n1:tm, n2:of n1 T3 |- a1 n1 n2 : of (R n1) T4}*
  
  ==================================
  exists D3, {G |- D3 : eq (arr T3 T4) T2}
  
  Subgoal ty_unique_aux.2 is:
   exists D3, {G |- D3 : eq T1 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.1>> cases H2.
  
  Subgoal ty_unique_aux.1:
  
  Vars: D3:(o) -> (o) -> o, T5:o, a1:(o) -> (o) -> o, R:(o) -> o, T3:o, T4:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:
      {G |- of_abs T3 T4 ([c13]R c13) ([c14][c15]a1 c14 c15) :
        of (abs T3 ([c4]R c4)) (arr T3 T4)}@
  H3:{G |- T3 : ty}*
  H4:{G |- T4 : ty}*
  H5:{G, n:tm |- R n : tm}*
  H6:{G, n1:tm, n2:of n1 T3 |- a1 n1 n2 : of (R n1) T4}*
  H7:{G |- T3 : ty}
  H8:{G |- T5 : ty}
  H9:{G, n3:tm |- R n3 : tm}
  H10:{G, n4:tm, n5:of n4 T3 |- D3 n4 n5 : of (R n4) T5}
  
  ==================================
  exists D3, {G |- D3 : eq (arr T3 T4) (arr T3 T5)}
  
  Subgoal ty_unique_aux.2 is:
   exists D3, {G |- D3 : eq T1 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.1>> apply IH to H6 H10 with (G = G,n1:tm,n:of n1 T3).
  
  Subgoal ty_unique_aux.1:
  
  Vars: D3:(o) -> (o) -> o, T5:o, a1:(o) -> (o) -> o, R:(o) -> o, T3:o, T4:o,
          D1:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:
      {G |- of_abs T3 T4 ([c13]R c13) ([c14][c15]a1 c14 c15) :
        of (abs T3 ([c4]R c4)) (arr T3 T4)}@
  H3:{G |- T3 : ty}*
  H4:{G |- T4 : ty}*
  H5:{G, n:tm |- R n : tm}*
  H6:{G, n1:tm, n2:of n1 T3 |- a1 n1 n2 : of (R n1) T4}*
  H7:{G |- T3 : ty}
  H8:{G |- T5 : ty}
  H9:{G, n3:tm |- R n3 : tm}
  H10:{G, n4:tm, n5:of n4 T3 |- D3 n4 n5 : of (R n4) T5}
  H11:{G, n1:tm, n:of n1 T3 |- D1 n5 n4 n3 n2 n1 n : eq T4 T5}
  
  ==================================
  exists D3, {G |- D3 : eq (arr T3 T4) (arr T3 T5)}
  
  Subgoal ty_unique_aux.2 is:
   exists D3, {G |- D3 : eq T1 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.1>> cases H11.
  
  Subgoal ty_unique_aux.1:
  
  Vars: D3:(o) -> (o) -> o, T5:o, a1:(o) -> (o) -> o, R:(o) -> o, T3:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:
      {G |- of_abs T3 T5 ([c13]R c13) ([c14][c15]a1 c14 c15) :
        of (abs T3 ([c4]R c4)) (arr T3 T5)}@
  H3:{G |- T3 : ty}*
  H4:{G |- T5 : ty}*
  H5:{G, n:tm |- R n : tm}*
  H6:{G, n1:tm, n2:of n1 T3 |- a1 n1 n2 : of (R n1) T5}*
  H7:{G |- T3 : ty}
  H8:{G |- T5 : ty}
  H9:{G, n3:tm |- R n3 : tm}
  H10:{G, n4:tm, n5:of n4 T3 |- D3 n4 n5 : of (R n4) T5}
  H12:{G, n1:tm, n:of n1 T3 |- T5 : ty}
  
  ==================================
  exists D3, {G |- D3 : eq (arr T3 T5) (arr T3 T5)}
  
  Subgoal ty_unique_aux.2 is:
   exists D3, {G |- D3 : eq T1 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.1>> exists refl arr T3 T4.
  
  Subgoal ty_unique_aux.1:
  
  Vars: D3:(o) -> (o) -> o, T5:o, a1:(o) -> (o) -> o, R:(o) -> o, T3:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:
      {G |- of_abs T3 T5 ([c13]R c13) ([c14][c15]a1 c14 c15) :
        of (abs T3 ([c4]R c4)) (arr T3 T5)}@
  H3:{G |- T3 : ty}*
  H4:{G |- T5 : ty}*
  H5:{G, n:tm |- R n : tm}*
  H6:{G, n1:tm, n2:of n1 T3 |- a1 n1 n2 : of (R n1) T5}*
  H7:{G |- T3 : ty}
  H8:{G |- T5 : ty}
  H9:{G, n3:tm |- R n3 : tm}
  H10:{G, n4:tm, n5:of n4 T3 |- D3 n4 n5 : of (R n4) T5}
  H12:{G, n1:tm, n:of n1 T3 |- T5 : ty}
  
  ==================================
  {G |- refl (arr T3 T5) : eq (arr T3 T5) (arr T3 T5)}
  
  Subgoal ty_unique_aux.2 is:
   exists D3, {G |- D3 : eq T1 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.1>> search.
  
  Subgoal ty_unique_aux.2:
  
  Vars: T3:o, a1:o, a2:o, M1:o, M2:o, D2:o, T2:o, T1:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- of_app M1 M2 T3 T1 a1 a2 : of (app M1 M2) T1}@
  H2:{G |- D2 : of (app M1 M2) T2}
  H3:{G |- M1 : tm}*
  H4:{G |- M2 : tm}*
  H5:{G |- T3 : ty}*
  H6:{G |- T1 : ty}*
  H7:{G |- a1 : of M1 (arr T3 T1)}*
  H8:{G |- a2 : of M2 T3}*
  
  ==================================
  exists D3, {G |- D3 : eq T1 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.2>> cases H2.
  
  Subgoal ty_unique_aux.2:
  
  Vars: T4:o, a3:o, a4:o, T3:o, a1:o, a2:o, M1:o, M2:o, T2:o, T1:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- of_app M1 M2 T3 T1 a1 a2 : of (app M1 M2) T1}@
  H3:{G |- M1 : tm}*
  H4:{G |- M2 : tm}*
  H5:{G |- T3 : ty}*
  H6:{G |- T1 : ty}*
  H7:{G |- a1 : of M1 (arr T3 T1)}*
  H8:{G |- a2 : of M2 T3}*
  H9:{G |- M1 : tm}
  H10:{G |- M2 : tm}
  H11:{G |- T4 : ty}
  H12:{G |- T2 : ty}
  H13:{G |- a3 : of M1 (arr T4 T2)}
  H14:{G |- a4 : of M2 T4}
  
  ==================================
  exists D3, {G |- D3 : eq T1 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.2>> apply IH to H7 H13.
  
  Subgoal ty_unique_aux.2:
  
  Vars: D3:o, T4:o, a3:o, a4:o, T3:o, a1:o, a2:o, M1:o, M2:o, T2:o, T1:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- of_app M1 M2 T3 T1 a1 a2 : of (app M1 M2) T1}@
  H3:{G |- M1 : tm}*
  H4:{G |- M2 : tm}*
  H5:{G |- T3 : ty}*
  H6:{G |- T1 : ty}*
  H7:{G |- a1 : of M1 (arr T3 T1)}*
  H8:{G |- a2 : of M2 T3}*
  H9:{G |- M1 : tm}
  H10:{G |- M2 : tm}
  H11:{G |- T4 : ty}
  H12:{G |- T2 : ty}
  H13:{G |- a3 : of M1 (arr T4 T2)}
  H14:{G |- a4 : of M2 T4}
  H15:{G |- D3 : eq (arr T3 T1) (arr T4 T2)}
  
  ==================================
  exists D3, {G |- D3 : eq T1 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.2>> cases H15.
  
  Subgoal ty_unique_aux.2:
  
  Vars: T4:o, a3:o, a4:o, a1:o, a2:o, M1:o, M2:o, T2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- of_app M1 M2 T4 T2 a1 a2 : of (app M1 M2) T2}@
  H3:{G |- M1 : tm}*
  H4:{G |- M2 : tm}*
  H5:{G |- T4 : ty}*
  H6:{G |- T2 : ty}*
  H7:{G |- a1 : of M1 (arr T4 T2)}*
  H8:{G |- a2 : of M2 T4}*
  H9:{G |- M1 : tm}
  H10:{G |- M2 : tm}
  H11:{G |- T4 : ty}
  H12:{G |- T2 : ty}
  H13:{G |- a3 : of M1 (arr T4 T2)}
  H14:{G |- a4 : of M2 T4}
  H16:{G |- arr T4 T2 : ty}
  
  ==================================
  exists D3, {G |- D3 : eq T2 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.2>> exists refl T2.
  
  Subgoal ty_unique_aux.2:
  
  Vars: T4:o, a3:o, a4:o, a1:o, a2:o, M1:o, M2:o, T2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- of_app M1 M2 T4 T2 a1 a2 : of (app M1 M2) T2}@
  H3:{G |- M1 : tm}*
  H4:{G |- M2 : tm}*
  H5:{G |- T4 : ty}*
  H6:{G |- T2 : ty}*
  H7:{G |- a1 : of M1 (arr T4 T2)}*
  H8:{G |- a2 : of M2 T4}*
  H9:{G |- M1 : tm}
  H10:{G |- M2 : tm}
  H11:{G |- T4 : ty}
  H12:{G |- T2 : ty}
  H13:{G |- a3 : of M1 (arr T4 T2)}
  H14:{G |- a4 : of M2 T4}
  H16:{G |- arr T4 T2 : ty}
  
  ==================================
  {G |- refl T2 : eq T2 T2}
  
  Subgoal ty_unique_aux.3 is:
   exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.2>> search.
  
  Subgoal ty_unique_aux.3:
  
  Vars: D2:(o) -> (o) -> o, T2:(o) -> (o) -> o, T1:(o) -> (o) -> o
  Nominals: n1:o, n:o
  Contexts: G{}:c[(n:tm, n1:of n (T1 n n1))]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- n1 : of n (T1 n n1)}@
  H2:{G |- D2 n n1 : of n (T2 n n1)}
  
  ==================================
  exists D3, {G |- D3 : eq (T1 n n1) (T2 n n1)}
  
  ty_unique_aux.3>> cases H2.
  
  Subgoal ty_unique_aux.3:
  
  Vars: T2:(o) -> (o) -> o
  Nominals: n1:o, n:o
  Contexts: G{}:c[(n:tm, n1:of n (T2 n n1))]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- n1 : of n (T2 n n1)}@
  
  ==================================
  exists D3, {G |- D3 : eq (T2 n n1) (T2 n n1)}
  
  ty_unique_aux.3>> exists refl T2 n n1.
  
  Subgoal ty_unique_aux.3:
  
  Vars: T2:(o) -> (o) -> o
  Nominals: n1:o, n:o
  Contexts: G{}:c[(n:tm, n1:of n (T2 n n1))]
  IH:
      ctx G:c,
        forall E, forall T1, forall T2, forall D1, forall D2,
          {G |- D1 : of E T1}* =>
              {G |- D2 : of E T2} => exists D3, {G |- D3 : eq T1 T2}
  H1:{G |- n1 : of n (T2 n n1)}@
  
  ==================================
  {G |- refl (T2 n n1) : eq (T2 n n1) (T2 n n1)}
  
  ty_unique_aux.3>> search.
  Proof Completed!
  
  >> Theorem ty_unique:
      ctx  G:c,
        forall  E T1 T2 D1 D2,
          {G |- D1 : of E T1} =>
            {G |- D2 : of E T2} => exists  D3, {D3 : eq T1 T2}.
  
  Subgoal ty_unique:
  
  
  ==================================
  ctx G:c,
    forall E, forall T1, forall T2, forall D1, forall D2,
      {G |- D1 : of E T1} => {G |- D2 : of E T2} => exists D3, {D3 : eq T1 T2}
  
  ty_unique>> intros.
  
  Subgoal ty_unique:
  
  Vars: D2:o, D1:o, T2:o, T1:o, E:o
  Contexts: G{}:c[]
  H1:{G |- D1 : of E T1}
  H2:{G |- D2 : of E T2}
  
  ==================================
  exists D3, {D3 : eq T1 T2}
  
  ty_unique>> apply ty_unique_aux to H1 H2.
  
  Subgoal ty_unique:
  
  Vars: D3:o, D2:o, D1:o, T2:o, T1:o, E:o
  Contexts: G{}:c[]
  H1:{G |- D1 : of E T1}
  H2:{G |- D2 : of E T2}
  H3:{G |- D3 : eq T1 T2}
  
  ==================================
  exists D3, {D3 : eq T1 T2}
  
  ty_unique>> apply eq_independent to H3.
  
  Subgoal ty_unique:
  
  Vars: D3:o, D2:o, D1:o, T2:o, T1:o, E:o
  Contexts: G{}:c[]
  H1:{G |- D1 : of E T1}
  H2:{G |- D2 : of E T2}
  H3:{G |- D3 : eq T1 T2}
  H4:{D3 : eq T1 T2}
  
  ==================================
  exists D3, {D3 : eq T1 T2}
  
  ty_unique>> exists D3.
  
  Subgoal ty_unique:
  
  Vars: D3:o, D2:o, D1:o, T2:o, T1:o, E:o
  Contexts: G{}:c[]
  H1:{G |- D1 : of E T1}
  H2:{G |- D2 : of E T2}
  H3:{G |- D3 : eq T1 T2}
  H4:{D3 : eq T1 T2}
  
  ==================================
  {D3 : eq T1 T2}
  
  ty_unique>> search.
  Proof Completed!
  
  >> Theorem self_app_untypable:
      forall  T U P,
        {P : of app abs U ([x]app x x) abs U ([x]app x x) T} => false.
  
  Subgoal self_app_untypable:
  
  
  ==================================
  forall T, forall U, forall P,
    {P : of (app (abs U ([x]app x x)) (abs U ([x]app x x))) T} => False
  
  self_app_untypable>> intros.
  
  Subgoal self_app_untypable:
  
  Vars: P:o, U:o, T:o
  H1:{P : of (app (abs U ([x]app x x)) (abs U ([x]app x x))) T}
  
  ==================================
  False
  
  self_app_untypable>> cases H1.
  
  Subgoal self_app_untypable:
  
  Vars: T1:o, a1:o, a2:o, U:o, T:o
  H2:{abs U ([x]app x x) : tm}
  H3:{abs U ([x]app x x) : tm}
  H4:{T1 : ty}
  H5:{T : ty}
  H6:{a1 : of (abs U ([x]app x x)) (arr T1 T)}
  H7:{a2 : of (abs U ([x]app x x)) T1}
  
  ==================================
  False
  
  self_app_untypable>> cases H6.
  
  Subgoal self_app_untypable:
  
  Vars: a3:(o) -> (o) -> o, T1:o, a2:o, T:o
  Nominals: n2:o, n1:o, n:o
  H2:{abs T1 ([x]app x x) : tm}
  H3:{abs T1 ([x]app x x) : tm}
  H4:{T1 : ty}
  H5:{T : ty}
  H7:{a2 : of (abs T1 ([x]app x x)) T1}
  H8:{T1 : ty}
  H9:{T : ty}
  H10:{n:tm |- app n n : tm}
  H11:{n1:tm, n2:of n1 T1 |- a3 n1 n2 : of (app n1 n1) T}
  
  ==================================
  False
  
  self_app_untypable>> cases H7.
  Proof Completed!
  
  >> Goodbye!
