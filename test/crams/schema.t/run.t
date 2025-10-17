  $ adelfa -i size.ath
  Welcome!
  >> Specification "size.lf".
  
  >> Theorem plus-exist:
      forall  N1 N2,
        {N1 : nat} => {N2 : nat} => exists  N3 D, {D : plus N1 N2 N3}.
  
  Subgoal plus-exist:
  
  
  ==================================
  forall N1, forall N2,
    {N1 : nat} => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  
  plus-exist>> induction on 1.
  
  Subgoal plus-exist:
  
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  
  ==================================
  forall N1, forall N2,
    {N1 : nat}@ => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  
  plus-exist>> intros.
  
  Subgoal plus-exist:
  
  Vars: N2:o, N1:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H1:{N1 : nat}@
  H2:{N2 : nat}
  
  ==================================
  exists N3, exists D, {D : plus N1 N2 N3}
  
  plus-exist>> cases H1.
  
  Subgoal plus-exist.1:
  
  Vars: x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  
  ==================================
  exists N3, exists D, {D : plus (s x) N2 N3}
  
  Subgoal plus-exist.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus-exist.1>> apply IH to H3 H2.
  
  Subgoal plus-exist.1:
  
  Vars: D:o, N3:o, x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  H4:{D : plus x N2 N3}
  
  ==================================
  exists N3, exists D, {D : plus (s x) N2 N3}
  
  Subgoal plus-exist.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus-exist.1>> exists s N3.
  
  Subgoal plus-exist.1:
  
  Vars: D:o, N3:o, x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  H4:{D : plus x N2 N3}
  
  ==================================
  exists D, {D : plus (s x) N2 (s N3)}
  
  Subgoal plus-exist.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus-exist.1>> exists plus-s x N2 N3 D.
  
  Subgoal plus-exist.1:
  
  Vars: D:o, N3:o, x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  H4:{D : plus x N2 N3}
  
  ==================================
  {plus-s x N2 N3 D : plus (s x) N2 (s N3)}
  
  Subgoal plus-exist.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus-exist.1>> search.
  
  Subgoal plus-exist.2:
  
  Vars: N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  
  ==================================
  exists N3, exists D, {D : plus z N2 N3}
  
  plus-exist.2>> exists N2.
  
  Subgoal plus-exist.2:
  
  Vars: N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  
  ==================================
  exists D, {D : plus z N2 N2}
  
  plus-exist.2>> exists plus-z N2.
  
  Subgoal plus-exist.2:
  
  Vars: N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  
  ==================================
  {plus-z N2 : plus z N2 N2}
  
  plus-exist.2>> search.
  Proof Completed!
  
  >> Schema c := {}(A:tm,y:size A s z).
  
  >> Theorem tm-has-size:
      ctx  G:c, forall  E, {G |- E : tm} => exists  D N, {G |- D : size E N}.
  
  Subgoal tm-has-size:
  
  
  ==================================
  ctx G:c, forall E, {G |- E : tm} => exists D, exists N, {G |- D : size E N}
  
  tm-has-size>> induction on 1.
  
  Subgoal tm-has-size:
  
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  
  ==================================
  ctx G:c, forall E, {G |- E : tm}@ => exists D, exists N, {G |- D : size E N}
  
  tm-has-size>> intros.
  
  Subgoal tm-has-size:
  
  Vars: E:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- E : tm}@
  
  ==================================
  exists D, exists N, {G |- D : size E N}
  
  tm-has-size>> cases H1.
  
  Subgoal tm-has-size.1:
  
  Vars: E1:(o) -> o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  
  ==================================
  exists D, exists N, {G |- D : size (lam ([c7]E1 c7)) N}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> weaken H2 with size n s z.
  
  Subgoal tm-has-size.1:
  
  Vars: E1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  H3:{G, n:tm, n1:size n (s z) |- E1 n : tm}*
  
  ==================================
  exists D, exists N, {G |- D : size (lam ([c7]E1 c7)) N}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> apply IH to H3 with (G = G,n1:tm,n:size n1 s z).
  
  Subgoal tm-has-size.1:
  
  Vars: N:(o) -> (o) -> o, D:(o) -> (o) -> o, E1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  H3:{G, n:tm, n1:size n (s z) |- E1 n : tm}*
  H4:{G, n1:tm, n:size n1 (s z) |- D n1 n : size (E1 n1) (N n1 n)}
  
  ==================================
  exists D, exists N, {G |- D : size (lam ([c7]E1 c7)) N}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> assert {G,n1:tm,n:size n1 s z |- N n1 n : nat}.
  
  Subgoal tm-has-size.1:
  
  Vars: N:(o) -> (o) -> o, D:(o) -> (o) -> o, E1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  H3:{G, n:tm, n1:size n (s z) |- E1 n : tm}*
  H4:{G, n1:tm, n:size n1 (s z) |- D n1 n : size (E1 n1) (N n1 n)}
  H5:{G, n1:tm, n:size n1 (s z) |- N n1 n : nat}
  
  ==================================
  exists D, exists N, {G |- D : size (lam ([c7]E1 c7)) N}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> prune H5.
  
  Subgoal tm-has-size.1:
  
  Vars: N:o, D:(o) -> (o) -> o, E1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  H3:{G, n:tm, n1:size n (s z) |- E1 n : tm}*
  H4:{G, n1:tm, n:size n1 (s z) |- D n1 n : size (E1 n1) N}
  H5:{G, n1:tm, n:size n1 (s z) |- N : nat}
  
  ==================================
  exists D, exists N, {G |- D : size (lam ([c7]E1 c7)) N}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> strengthen H5.
  
  Subgoal tm-has-size.1:
  
  Vars: N:o, D:(o) -> (o) -> o, E1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  H3:{G, n:tm, n1:size n (s z) |- E1 n : tm}*
  H4:{G, n1:tm, n:size n1 (s z) |- D n1 n : size (E1 n1) N}
  H5:{G, n1:tm, n:size n1 (s z) |- N : nat}
  H6:{G, n1:tm |- N : nat}
  
  ==================================
  exists D, exists N, {G |- D : size (lam ([c7]E1 c7)) N}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> strengthen H6.
  
  Subgoal tm-has-size.1:
  
  Vars: N:o, D:(o) -> (o) -> o, E1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  H3:{G, n:tm, n1:size n (s z) |- E1 n : tm}*
  H4:{G, n1:tm, n:size n1 (s z) |- D n1 n : size (E1 n1) N}
  H5:{G, n1:tm, n:size n1 (s z) |- N : nat}
  H6:{G, n1:tm |- N : nat}
  H7:{G |- N : nat}
  
  ==================================
  exists D, exists N, {G |- D : size (lam ([c7]E1 c7)) N}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> exists size-lam ([x]E1 x) N D.
  
  Subgoal tm-has-size.1:
  
  Vars: N:o, D:(o) -> (o) -> o, E1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  H3:{G, n:tm, n1:size n (s z) |- E1 n : tm}*
  H4:{G, n1:tm, n:size n1 (s z) |- D n1 n : size (E1 n1) N}
  H5:{G, n1:tm, n:size n1 (s z) |- N : nat}
  H6:{G, n1:tm |- N : nat}
  H7:{G |- N : nat}
  
  ==================================
  exists N1, {G |- size-lam ([x]E1 x) N D : size (lam ([c7]E1 c7)) N1}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> exists s N.
  
  Subgoal tm-has-size.1:
  
  Vars: N:o, D:(o) -> (o) -> o, E1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- lam ([c2]E1 c2) : tm}@
  H2:{G, n:tm |- E1 n : tm}*
  H3:{G, n:tm, n1:size n (s z) |- E1 n : tm}*
  H4:{G, n1:tm, n:size n1 (s z) |- D n1 n : size (E1 n1) N}
  H5:{G, n1:tm, n:size n1 (s z) |- N : nat}
  H6:{G, n1:tm |- N : nat}
  H7:{G |- N : nat}
  
  ==================================
  {G |- size-lam ([x]E1 x) N D : size (lam ([c7]E1 c7)) (s N)}
  
  Subgoal tm-has-size.2 is:
   exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.1>> search.
  
  Subgoal tm-has-size.2:
  
  Vars: E1:o, E2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- app E1 E2 : tm}@
  H2:{G |- E1 : tm}*
  H3:{G |- E2 : tm}*
  
  ==================================
  exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.2>> apply IH to H2.
  
  Subgoal tm-has-size.2:
  
  Vars: N:o, D:o, E1:o, E2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- app E1 E2 : tm}@
  H2:{G |- E1 : tm}*
  H3:{G |- E2 : tm}*
  H4:{G |- D : size E1 N}
  
  ==================================
  exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.2>> apply IH to H3.
  
  Subgoal tm-has-size.2:
  
  Vars: N1:o, D1:o, N:o, D:o, E1:o, E2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- app E1 E2 : tm}@
  H2:{G |- E1 : tm}*
  H3:{G |- E2 : tm}*
  H4:{G |- D : size E1 N}
  H5:{G |- D1 : size E2 N1}
  
  ==================================
  exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.2>> assert {G |- N : nat}.
  
  Subgoal tm-has-size.2:
  
  Vars: N1:o, D1:o, N:o, D:o, E1:o, E2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- app E1 E2 : tm}@
  H2:{G |- E1 : tm}*
  H3:{G |- E2 : tm}*
  H4:{G |- D : size E1 N}
  H5:{G |- D1 : size E2 N1}
  H6:{G |- N : nat}
  
  ==================================
  exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.2>> assert {G |- N1 : nat}.
  
  Subgoal tm-has-size.2:
  
  Vars: N1:o, D1:o, N:o, D:o, E1:o, E2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- app E1 E2 : tm}@
  H2:{G |- E1 : tm}*
  H3:{G |- E2 : tm}*
  H4:{G |- D : size E1 N}
  H5:{G |- D1 : size E2 N1}
  H6:{G |- N : nat}
  H7:{G |- N1 : nat}
  
  ==================================
  exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.2>> apply plus-exist to H6 H7.
  
  Subgoal tm-has-size.2:
  
  Vars: D2:o, N3:o, N1:o, D1:o, N:o, D:o, E1:o, E2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- app E1 E2 : tm}@
  H2:{G |- E1 : tm}*
  H3:{G |- E2 : tm}*
  H4:{G |- D : size E1 N}
  H5:{G |- D1 : size E2 N1}
  H6:{G |- N : nat}
  H7:{G |- N1 : nat}
  H8:{G |- D2 : plus N N1 N3}
  
  ==================================
  exists D, exists N, {G |- D : size (app E1 E2) N}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.2>> exists size-app E1 E2 N N1 N3 D D1 D2.
  
  Subgoal tm-has-size.2:
  
  Vars: D2:o, N3:o, N1:o, D1:o, N:o, D:o, E1:o, E2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- app E1 E2 : tm}@
  H2:{G |- E1 : tm}*
  H3:{G |- E2 : tm}*
  H4:{G |- D : size E1 N}
  H5:{G |- D1 : size E2 N1}
  H6:{G |- N : nat}
  H7:{G |- N1 : nat}
  H8:{G |- D2 : plus N N1 N3}
  
  ==================================
  exists N2, {G |- size-app E1 E2 N N1 N3 D D1 D2 : size (app E1 E2) N2}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.2>> exists s N3.
  
  Subgoal tm-has-size.2:
  
  Vars: D2:o, N3:o, N1:o, D1:o, N:o, D:o, E1:o, E2:o
  Contexts: G{}:c[]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- app E1 E2 : tm}@
  H2:{G |- E1 : tm}*
  H3:{G |- E2 : tm}*
  H4:{G |- D : size E1 N}
  H5:{G |- D1 : size E2 N1}
  H6:{G |- N : nat}
  H7:{G |- N1 : nat}
  H8:{G |- D2 : plus N N1 N3}
  
  ==================================
  {G |- size-app E1 E2 N N1 N3 D D1 D2 : size (app E1 E2) (s N3)}
  
  Subgoal tm-has-size.3 is:
   exists D, exists N, {G |- D : size n N}
  
  tm-has-size.2>> search.
  
  Subgoal tm-has-size.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:c[(n:tm, n1:size n (s z))]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- n : tm}@
  
  ==================================
  exists D, exists N, {G |- D : size n N}
  
  tm-has-size.3>> exists n1.
  
  Subgoal tm-has-size.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:c[(n:tm, n1:size n (s z))]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- n : tm}@
  
  ==================================
  exists N, {G |- n1 : size n N}
  
  tm-has-size.3>> exists s z.
  
  Subgoal tm-has-size.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:c[(n:tm, n1:size n (s z))]
  IH:
      ctx G:c,
        forall E, {G |- E : tm}* => exists D, exists N, {G |- D : size E N}
  H1:{G |- n : tm}@
  
  ==================================
  {G |- n1 : size n (s z)}
  
  tm-has-size.3>> search.
  Proof Completed!
  
  >> Goodbye!
