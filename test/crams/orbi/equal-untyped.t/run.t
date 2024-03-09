  $ adelfa -i equal-untyped.ath
  Welcome!
  >> Specification equal-untyped.lf.
  
  >> Schema xG := {}(x:tm).
  
  >> Schema xaG := {}(x:tm,a:aeq x x).
  
  >> Schema daG := {}(x:tm,a:aeq x x,u:deq x x).
  
  >> Theorem reflG:
      ctx  G:xaG, forall  T, {G |- T : tm} => exists  D, {G |- D : aeq T T}.
  
  Subgoal reflG:
  
  
  ==================================
  ctx G:xaG, forall T, {G |- T : tm} => exists D, {G |- D : aeq T T}
  
  reflG>> induction on 1.
  
  Subgoal reflG:
  
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  
  ==================================
  ctx G:xaG, forall T, {G |- T : tm}@ => exists D, {G |- D : aeq T T}
  
  reflG>> intros.
  
  Subgoal reflG:
  
  Vars: T:o
  Contexts: G{}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- T : tm}@
  
  ==================================
  exists D, {G |- D : aeq T T}
  
  reflG>> cases H1.
  
  Subgoal reflG.1:
  
  Vars: M1:o, M2:o
  Contexts: G{}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- app M1 M2 : tm}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  
  ==================================
  exists D, {G |- D : aeq (app M1 M2) (app M1 M2)}
  
  Subgoal reflG.2 is:
   exists D, {G |- D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.1>> apply IH to H2.
  
  Subgoal reflG.1:
  
  Vars: D:o, M1:o, M2:o
  Contexts: G{}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- app M1 M2 : tm}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- D : aeq M1 M1}
  
  ==================================
  exists D, {G |- D : aeq (app M1 M2) (app M1 M2)}
  
  Subgoal reflG.2 is:
   exists D, {G |- D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.1>> apply IH to H3.
  
  Subgoal reflG.1:
  
  Vars: D1:o, D:o, M1:o, M2:o
  Contexts: G{}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- app M1 M2 : tm}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- D : aeq M1 M1}
  H5:{G |- D1 : aeq M2 M2}
  
  ==================================
  exists D, {G |- D : aeq (app M1 M2) (app M1 M2)}
  
  Subgoal reflG.2 is:
   exists D, {G |- D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.1>> exists ae_a M1 M2 M1 M2 D D1.
  
  Subgoal reflG.1:
  
  Vars: D1:o, D:o, M1:o, M2:o
  Contexts: G{}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- app M1 M2 : tm}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- D : aeq M1 M1}
  H5:{G |- D1 : aeq M2 M2}
  
  ==================================
  {G |- ae_a M1 M2 M1 M2 D D1 : aeq (app M1 M2) (app M1 M2)}
  
  Subgoal reflG.2 is:
   exists D, {G |- D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.1>> search.
  
  Subgoal reflG.2:
  
  Vars: M:(o) -> o
  Nominals: n:o
  Contexts: G{n}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- lam ([c4]M c4) : tm}@
  H2:{G, n:tm |- M n : tm}*
  
  ==================================
  exists D, {G |- D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.2>> weaken H2 with aeq n n.
  
  Subgoal reflG.2:
  
  Vars: M:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- lam ([c4]M c4) : tm}@
  H2:{G, n:tm |- M n : tm}*
  H3:{G, n:tm, n1:aeq n n |- M n : tm}*
  
  ==================================
  exists D, {G |- D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.2>> apply IH to H3 with (G = G,n1:tm,n:aeq n1 n1).
  
  Subgoal reflG.2:
  
  Vars: D:(o) -> (o) -> o, M:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- lam ([c4]M c4) : tm}@
  H2:{G, n:tm |- M n : tm}*
  H3:{G, n:tm, n1:aeq n n |- M n : tm}*
  H4:{G, n1:tm, n:aeq n1 n1 |- D n1 n : aeq (M n1) (M n1)}
  
  ==================================
  exists D, {G |- D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.2>> prune H2.
  
  Subgoal reflG.2:
  
  Vars: D:(o) -> (o) -> o, M:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- lam ([c4]M c4) : tm}@
  H2:{G, n:tm |- M n : tm}*
  H3:{G, n:tm, n1:aeq n n |- M n : tm}*
  H4:{G, n1:tm, n:aeq n1 n1 |- D n1 n : aeq (M n1) (M n1)}
  
  ==================================
  exists D, {G |- D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.2>> exists ae_l M M D.
  
  Subgoal reflG.2:
  
  Vars: D:(o) -> (o) -> o, M:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- lam ([c4]M c4) : tm}@
  H2:{G, n:tm |- M n : tm}*
  H3:{G, n:tm, n1:aeq n n |- M n : tm}*
  H4:{G, n1:tm, n:aeq n1 n1 |- D n1 n : aeq (M n1) (M n1)}
  
  ==================================
  {G |- ae_l M M D : aeq (lam ([c13]M c13)) (lam ([c16]M c16))}
  
  Subgoal reflG.3 is:
   exists D, {G |- D : aeq n n}
  
  reflG.2>> search.
  
  Subgoal reflG.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:xaG[(n:tm, n1:aeq n n)]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- n : tm}@
  
  ==================================
  exists D, {G |- D : aeq n n}
  
  reflG.3>> exists n1.
  
  Subgoal reflG.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:xaG[(n:tm, n1:aeq n n)]
  IH:ctx G:xaG, forall T, {G |- T : tm}* => exists D, {G |- D : aeq T T}
  H1:{G |- n : tm}@
  
  ==================================
  {G |- n1 : aeq n n}
  
  reflG.3>> search.
  Proof Completed!
  
  >> Theorem symG:
      ctx  G:xaG,
        forall  T1 T2 Q,
          {G |- Q : aeq T1 T2} => exists  D, {G |- D : aeq T2 T1}.
  
  Subgoal symG:
  
  
  ==================================
  ctx G:xaG,
    forall T1, forall T2, forall Q,
      {G |- Q : aeq T1 T2} => exists D, {G |- D : aeq T2 T1}
  
  symG>> induction on 1.
  
  Subgoal symG:
  
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  
  ==================================
  ctx G:xaG,
    forall T1, forall T2, forall Q,
      {G |- Q : aeq T1 T2}@ => exists D, {G |- D : aeq T2 T1}
  
  symG>> intros.
  
  Subgoal symG:
  
  Vars: Q:o, T2:o, T1:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:{G |- Q : aeq T1 T2}@
  
  ==================================
  exists D, {G |- D : aeq T2 T1}
  
  symG>> cases H1.
  
  Subgoal symG.1:
  
  Vars: D:(o) -> (o) -> o, M:(o) -> o, N:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H2:{G, n:tm |- M n : tm}*
  H3:{G, n1:tm |- N n1 : tm}*
  H4:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  
  ==================================
  exists D, {G |- D : aeq (lam ([c32]N c32)) (lam ([c35]M c35))}
  
  Subgoal symG.2 is:
   exists D, {G |- D : aeq (app N1 N2) (app M1 M2)}
  
  Subgoal symG.3 is:
   exists D, {G |- D : aeq n n}
  
  symG.1>> apply IH to H4 with (G = G,n1:tm,n:aeq n1 n1).
  
  Subgoal symG.1:
  
  Vars: D1:(o) -> (o) -> (o) -> (o) -> o, D:(o) -> (o) -> o, M:(o) -> o, N:
          (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H2:{G, n:tm |- M n : tm}*
  H3:{G, n1:tm |- N n1 : tm}*
  H4:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  H5:{G, n1:tm, n:aeq n1 n1 |- D1 n3 n2 n1 n : aeq (N n1) (M n1)}
  
  ==================================
  exists D, {G |- D : aeq (lam ([c32]N c32)) (lam ([c35]M c35))}
  
  Subgoal symG.2 is:
   exists D, {G |- D : aeq (app N1 N2) (app M1 M2)}
  
  Subgoal symG.3 is:
   exists D, {G |- D : aeq n n}
  
  symG.1>> prune H5.
  
  Subgoal symG.1:
  
  Vars: D1:(o) -> (o) -> o, D:(o) -> (o) -> o, M:(o) -> o, N:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H2:{G, n:tm |- M n : tm}*
  H3:{G, n1:tm |- N n1 : tm}*
  H4:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  H5:{G, n1:tm, n:aeq n1 n1 |- D1 n1 n : aeq (N n1) (M n1)}
  
  ==================================
  exists D, {G |- D : aeq (lam ([c32]N c32)) (lam ([c35]M c35))}
  
  Subgoal symG.2 is:
   exists D, {G |- D : aeq (app N1 N2) (app M1 M2)}
  
  Subgoal symG.3 is:
   exists D, {G |- D : aeq n n}
  
  symG.1>> exists ae_l N M D1.
  
  Subgoal symG.1:
  
  Vars: D1:(o) -> (o) -> o, D:(o) -> (o) -> o, M:(o) -> o, N:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H2:{G, n:tm |- M n : tm}*
  H3:{G, n1:tm |- N n1 : tm}*
  H4:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  H5:{G, n1:tm, n:aeq n1 n1 |- D1 n1 n : aeq (N n1) (M n1)}
  
  ==================================
  {G |- ae_l N M D1 : aeq (lam ([c32]N c32)) (lam ([c35]M c35))}
  
  Subgoal symG.2 is:
   exists D, {G |- D : aeq (app N1 N2) (app M1 M2)}
  
  Subgoal symG.3 is:
   exists D, {G |- D : aeq n n}
  
  symG.1>> search.
  
  Subgoal symG.2:
  
  Vars: D1:o, D2:o, M1:o, M2:o, N1:o, N2:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:{G |- ae_a M1 M2 N1 N2 D1 D2 : aeq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D1 : aeq M1 N1}*
  H7:{G |- D2 : aeq M2 N2}*
  
  ==================================
  exists D, {G |- D : aeq (app N1 N2) (app M1 M2)}
  
  Subgoal symG.3 is:
   exists D, {G |- D : aeq n n}
  
  symG.2>> apply IH to H6.
  
  Subgoal symG.2:
  
  Vars: D:o, D1:o, D2:o, M1:o, M2:o, N1:o, N2:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:{G |- ae_a M1 M2 N1 N2 D1 D2 : aeq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D1 : aeq M1 N1}*
  H7:{G |- D2 : aeq M2 N2}*
  H8:{G |- D : aeq N1 M1}
  
  ==================================
  exists D, {G |- D : aeq (app N1 N2) (app M1 M2)}
  
  Subgoal symG.3 is:
   exists D, {G |- D : aeq n n}
  
  symG.2>> apply IH to H7.
  
  Subgoal symG.2:
  
  Vars: D3:o, D:o, D1:o, D2:o, M1:o, M2:o, N1:o, N2:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:{G |- ae_a M1 M2 N1 N2 D1 D2 : aeq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D1 : aeq M1 N1}*
  H7:{G |- D2 : aeq M2 N2}*
  H8:{G |- D : aeq N1 M1}
  H9:{G |- D3 : aeq N2 M2}
  
  ==================================
  exists D, {G |- D : aeq (app N1 N2) (app M1 M2)}
  
  Subgoal symG.3 is:
   exists D, {G |- D : aeq n n}
  
  symG.2>> exists ae_a N1 N2 M1 M2 D D3.
  
  Subgoal symG.2:
  
  Vars: D3:o, D:o, D1:o, D2:o, M1:o, M2:o, N1:o, N2:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:{G |- ae_a M1 M2 N1 N2 D1 D2 : aeq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D1 : aeq M1 N1}*
  H7:{G |- D2 : aeq M2 N2}*
  H8:{G |- D : aeq N1 M1}
  H9:{G |- D3 : aeq N2 M2}
  
  ==================================
  {G |- ae_a N1 N2 M1 M2 D D3 : aeq (app N1 N2) (app M1 M2)}
  
  Subgoal symG.3 is:
   exists D, {G |- D : aeq n n}
  
  symG.2>> search.
  
  Subgoal symG.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:xaG[(n:tm, n1:aeq n n)]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:{G |- n1 : aeq n n}@
  
  ==================================
  exists D, {G |- D : aeq n n}
  
  symG.3>> exists n1.
  
  Subgoal symG.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:xaG[(n:tm, n1:aeq n n)]
  IH:
      ctx G:xaG,
        forall T1, forall T2, forall Q,
          {G |- Q : aeq T1 T2}* => exists D, {G |- D : aeq T2 T1}
  H1:{G |- n1 : aeq n n}@
  
  ==================================
  {G |- n1 : aeq n n}
  
  symG.3>> search.
  Proof Completed!
  
  >> Theorem tranG:
      ctx  G:xaG,
        forall  M1 M2 M3 D1 D2,
          {G |- D1 : aeq M1 M2} =>
            {G |- D2 : aeq M2 M3} => exists  D3, {G |- D3 : aeq M1 M3}.
  
  Subgoal tranG:
  
  
  ==================================
  ctx G:xaG,
    forall M1, forall M2, forall M3, forall D1, forall D2,
      {G |- D1 : aeq M1 M2} =>
          {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  
  tranG>> induction on 1.
  
  Subgoal tranG:
  
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  
  ==================================
  ctx G:xaG,
    forall M1, forall M2, forall M3, forall D1, forall D2,
      {G |- D1 : aeq M1 M2}@ =>
          {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  
  tranG>> intros.
  
  Subgoal tranG:
  
  Vars: D2:o, D1:o, M3:o, M2:o, M1:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- D1 : aeq M1 M2}@
  H2:{G |- D2 : aeq M2 M3}
  
  ==================================
  exists D3, {G |- D3 : aeq M1 M3}
  
  tranG>> cases H1.
  
  Subgoal tranG.1:
  
  Vars: D:(o) -> (o) -> o, M:(o) -> o, N:(o) -> o, D2:o, M3:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H2:{G |- D2 : aeq (lam ([c6]N c6)) M3}
  H3:{G, n:tm |- M n : tm}*
  H4:{G, n1:tm |- N n1 : tm}*
  H5:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c32]M c32)) M3}
  
  Subgoal tranG.2 is:
   exists D3, {G |- D3 : aeq (app M4 M5) M3}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.1>> cases H2.
  
  Subgoal tranG.1:
  
  Vars: D3:(o) -> (o) -> o, M4:(o) -> o, D:(o) -> (o) -> o, M:(o) -> o, N:
          (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H3:{G, n:tm |- M n : tm}*
  H4:{G, n1:tm |- N n1 : tm}*
  H5:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  H6:{G, n4:tm |- N n4 : tm}
  H7:{G, n5:tm |- M4 n5 : tm}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D3 n6 n7 : aeq (N n6) (M4 n6)}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c74]M c74)) (lam ([c77]M4 c77))}
  
  Subgoal tranG.2 is:
   exists D3, {G |- D3 : aeq (app M4 M5) M3}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.1>> apply IH to H5 H8 with (G = G,n1:tm,n:aeq n1 n1).
  
  Subgoal tranG.1:
  
  Vars: D3:(o) -> (o) -> o, M4:(o) -> o, D:(o) -> (o) -> o, M:(o) -> o, N:
          (o) -> o, D1:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H3:{G, n:tm |- M n : tm}*
  H4:{G, n1:tm |- N n1 : tm}*
  H5:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  H6:{G, n4:tm |- N n4 : tm}
  H7:{G, n5:tm |- M4 n5 : tm}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D3 n6 n7 : aeq (N n6) (M4 n6)}
  H9:{G, n1:tm, n:aeq n1 n1 |- D1 n7 n6 n5 n4 n3 n2 n1 n : aeq (M n1) (M4 n1)}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c74]M c74)) (lam ([c77]M4 c77))}
  
  Subgoal tranG.2 is:
   exists D3, {G |- D3 : aeq (app M4 M5) M3}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.1>> prune H9.
  
  Subgoal tranG.1:
  
  Vars: D3:(o) -> (o) -> o, M4:(o) -> o, D:(o) -> (o) -> o, M:(o) -> o, N:
          (o) -> o, D1:(o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H3:{G, n:tm |- M n : tm}*
  H4:{G, n1:tm |- N n1 : tm}*
  H5:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  H6:{G, n4:tm |- N n4 : tm}
  H7:{G, n5:tm |- M4 n5 : tm}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D3 n6 n7 : aeq (N n6) (M4 n6)}
  H9:{G, n1:tm, n:aeq n1 n1 |- D1 n1 n : aeq (M n1) (M4 n1)}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c74]M c74)) (lam ([c77]M4 c77))}
  
  Subgoal tranG.2 is:
   exists D3, {G |- D3 : aeq (app M4 M5) M3}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.1>> exists ae_l M M4 D1.
  
  Subgoal tranG.1:
  
  Vars: D3:(o) -> (o) -> o, M4:(o) -> o, D:(o) -> (o) -> o, M:(o) -> o, N:
          (o) -> o, D1:(o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:
      {G |- ae_l ([c12]M c12) ([c13]N c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M c3)) (lam ([c6]N c6))}@
  H3:{G, n:tm |- M n : tm}*
  H4:{G, n1:tm |- N n1 : tm}*
  H5:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M n2) (N n2)}*
  H6:{G, n4:tm |- N n4 : tm}
  H7:{G, n5:tm |- M4 n5 : tm}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D3 n6 n7 : aeq (N n6) (M4 n6)}
  H9:{G, n1:tm, n:aeq n1 n1 |- D1 n1 n : aeq (M n1) (M4 n1)}
  
  ==================================
  {G |- ae_l M M4 D1 : aeq (lam ([c74]M c74)) (lam ([c77]M4 c77))}
  
  Subgoal tranG.2 is:
   exists D3, {G |- D3 : aeq (app M4 M5) M3}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.1>> search.
  
  Subgoal tranG.2:
  
  Vars: D3:o, D4:o, M4:o, M5:o, N1:o, N2:o, D2:o, M3:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- ae_a M4 M5 N1 N2 D3 D4 : aeq (app M4 M5) (app N1 N2)}@
  H2:{G |- D2 : aeq (app N1 N2) M3}
  H3:{G |- M4 : tm}*
  H4:{G |- M5 : tm}*
  H5:{G |- N1 : tm}*
  H6:{G |- N2 : tm}*
  H7:{G |- D3 : aeq M4 N1}*
  H8:{G |- D4 : aeq M5 N2}*
  
  ==================================
  exists D3, {G |- D3 : aeq (app M4 M5) M3}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.2>> cases H2.
  
  Subgoal tranG.2:
  
  Vars: D5:o, D6:o, N3:o, N4:o, D3:o, D4:o, M4:o, M5:o, N1:o, N2:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- ae_a M4 M5 N1 N2 D3 D4 : aeq (app M4 M5) (app N1 N2)}@
  H3:{G |- M4 : tm}*
  H4:{G |- M5 : tm}*
  H5:{G |- N1 : tm}*
  H6:{G |- N2 : tm}*
  H7:{G |- D3 : aeq M4 N1}*
  H8:{G |- D4 : aeq M5 N2}*
  H9:{G |- N1 : tm}
  H10:{G |- N2 : tm}
  H11:{G |- N3 : tm}
  H12:{G |- N4 : tm}
  H13:{G |- D5 : aeq N1 N3}
  H14:{G |- D6 : aeq N2 N4}
  
  ==================================
  exists D3, {G |- D3 : aeq (app M4 M5) (app N3 N4)}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.2>> apply IH to H7 H13.
  
  Subgoal tranG.2:
  
  Vars: D5:o, D6:o, N3:o, N4:o, D3:o, D4:o, M4:o, M5:o, N1:o, N2:o, D1:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- ae_a M4 M5 N1 N2 D3 D4 : aeq (app M4 M5) (app N1 N2)}@
  H3:{G |- M4 : tm}*
  H4:{G |- M5 : tm}*
  H5:{G |- N1 : tm}*
  H6:{G |- N2 : tm}*
  H7:{G |- D3 : aeq M4 N1}*
  H8:{G |- D4 : aeq M5 N2}*
  H9:{G |- N1 : tm}
  H10:{G |- N2 : tm}
  H11:{G |- N3 : tm}
  H12:{G |- N4 : tm}
  H13:{G |- D5 : aeq N1 N3}
  H14:{G |- D6 : aeq N2 N4}
  H15:{G |- D1 : aeq M4 N3}
  
  ==================================
  exists D3, {G |- D3 : aeq (app M4 M5) (app N3 N4)}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.2>> apply IH to H8 H14.
  
  Subgoal tranG.2:
  
  Vars: D5:o, D6:o, N3:o, N4:o, D3:o, D4:o, M4:o, M5:o, N1:o, N2:o, D2:o, D1:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- ae_a M4 M5 N1 N2 D3 D4 : aeq (app M4 M5) (app N1 N2)}@
  H3:{G |- M4 : tm}*
  H4:{G |- M5 : tm}*
  H5:{G |- N1 : tm}*
  H6:{G |- N2 : tm}*
  H7:{G |- D3 : aeq M4 N1}*
  H8:{G |- D4 : aeq M5 N2}*
  H9:{G |- N1 : tm}
  H10:{G |- N2 : tm}
  H11:{G |- N3 : tm}
  H12:{G |- N4 : tm}
  H13:{G |- D5 : aeq N1 N3}
  H14:{G |- D6 : aeq N2 N4}
  H15:{G |- D1 : aeq M4 N3}
  H16:{G |- D2 : aeq M5 N4}
  
  ==================================
  exists D3, {G |- D3 : aeq (app M4 M5) (app N3 N4)}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.2>> exists ae_a M4 M5 N3 N4 D1 D2.
  
  Subgoal tranG.2:
  
  Vars: D5:o, D6:o, N3:o, N4:o, D3:o, D4:o, M4:o, M5:o, N1:o, N2:o, D2:o, D1:o
  Contexts: G{}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- ae_a M4 M5 N1 N2 D3 D4 : aeq (app M4 M5) (app N1 N2)}@
  H3:{G |- M4 : tm}*
  H4:{G |- M5 : tm}*
  H5:{G |- N1 : tm}*
  H6:{G |- N2 : tm}*
  H7:{G |- D3 : aeq M4 N1}*
  H8:{G |- D4 : aeq M5 N2}*
  H9:{G |- N1 : tm}
  H10:{G |- N2 : tm}
  H11:{G |- N3 : tm}
  H12:{G |- N4 : tm}
  H13:{G |- D5 : aeq N1 N3}
  H14:{G |- D6 : aeq N2 N4}
  H15:{G |- D1 : aeq M4 N3}
  H16:{G |- D2 : aeq M5 N4}
  
  ==================================
  {G |- ae_a M4 M5 N3 N4 D1 D2 : aeq (app M4 M5) (app N3 N4)}
  
  Subgoal tranG.3 is:
   exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.2>> search.
  
  Subgoal tranG.3:
  
  Vars: D2:(o) -> (o) -> o, M3:(o) -> (o) -> o
  Nominals: n1:o, n:o
  Contexts: G{}:xaG[(n:tm, n1:aeq n n)]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- n1 : aeq n n}@
  H2:{G |- D2 n n1 : aeq n (M3 n n1)}
  
  ==================================
  exists D3, {G |- D3 : aeq n (M3 n n1)}
  
  tranG.3>> cases H2.
  
  Subgoal tranG.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:xaG[(n:tm, n1:aeq n n)]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- n1 : aeq n n}@
  
  ==================================
  exists D3, {G |- D3 : aeq n n}
  
  tranG.3>> exists n1.
  
  Subgoal tranG.3:
  
  Nominals: n1:o, n:o
  Contexts: G{}:xaG[(n:tm, n1:aeq n n)]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall M3, forall D1, forall D2,
          {G |- D1 : aeq M1 M2}* =>
              {G |- D2 : aeq M2 M3} => exists D3, {G |- D3 : aeq M1 M3}
  H1:{G |- n1 : aeq n n}@
  
  ==================================
  {G |- n1 : aeq n n}
  
  tranG.3>> search.
  Proof Completed!
  
  >> Theorem ceqG:
      ctx  G:daG,
        forall  M N D1, {G |- D1 : deq M N} => exists  D2, {G |- D2 : aeq M N}.
  
  Subgoal ceqG:
  
  
  ==================================
  ctx G:daG,
    forall M, forall N, forall D1,
      {G |- D1 : deq M N} => exists D2, {G |- D2 : aeq M N}
  
  ceqG>> induction on 1.
  
  Subgoal ceqG:
  
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  
  ==================================
  ctx G:daG,
    forall M, forall N, forall D1,
      {G |- D1 : deq M N}@ => exists D2, {G |- D2 : aeq M N}
  
  ceqG>> intros.
  
  Subgoal ceqG:
  
  Vars: D1:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- D1 : deq M N}@
  
  ==================================
  exists D2, {G |- D2 : aeq M N}
  
  ceqG>> cases H1.
  
  Subgoal ceqG.1:
  
  Vars: M2:o, D2:o, D3:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_t M M2 N D2 D3 : deq M N}@
  H2:{G |- M : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N : tm}*
  H5:{G |- D2 : deq M M2}*
  H6:{G |- D3 : deq M2 N}*
  
  ==================================
  exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.2 is:
   exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.1>> apply IH to H5.
  
  Subgoal ceqG.1:
  
  Vars: M2:o, D2:o, D3:o, D1:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_t M M2 N D2 D3 : deq M N}@
  H2:{G |- M : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N : tm}*
  H5:{G |- D2 : deq M M2}*
  H6:{G |- D3 : deq M2 N}*
  H7:{G |- D1 : aeq M M2}
  
  ==================================
  exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.2 is:
   exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.1>> apply IH to H6.
  
  Subgoal ceqG.1:
  
  Vars: D4:o, M2:o, D2:o, D3:o, D1:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_t M M2 N D2 D3 : deq M N}@
  H2:{G |- M : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N : tm}*
  H5:{G |- D2 : deq M M2}*
  H6:{G |- D3 : deq M2 N}*
  H7:{G |- D1 : aeq M M2}
  H8:{G |- D4 : aeq M2 N}
  
  ==================================
  exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.2 is:
   exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.1>> apply tranG to H7 H8.
  
  Subgoal ceqG.1:
  
  Vars: D5:o, D4:o, M2:o, D2:o, D3:o, D1:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_t M M2 N D2 D3 : deq M N}@
  H2:{G |- M : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N : tm}*
  H5:{G |- D2 : deq M M2}*
  H6:{G |- D3 : deq M2 N}*
  H7:{G |- D1 : aeq M M2}
  H8:{G |- D4 : aeq M2 N}
  H9:{G |- D5 : aeq M N}
  
  ==================================
  exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.2 is:
   exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.1>> exists D5.
  
  Subgoal ceqG.1:
  
  Vars: D5:o, D4:o, M2:o, D2:o, D3:o, D1:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_t M M2 N D2 D3 : deq M N}@
  H2:{G |- M : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N : tm}*
  H5:{G |- D2 : deq M M2}*
  H6:{G |- D3 : deq M2 N}*
  H7:{G |- D1 : aeq M M2}
  H8:{G |- D4 : aeq M2 N}
  H9:{G |- D5 : aeq M N}
  
  ==================================
  {G |- D5 : aeq M N}
  
  Subgoal ceqG.2 is:
   exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.1>> search.
  
  Subgoal ceqG.2:
  
  Vars: D:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_s N M D : deq M N}@
  H2:{G |- N : tm}*
  H3:{G |- M : tm}*
  H4:{G |- D : deq N M}*
  
  ==================================
  exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.2>> apply IH to H4.
  
  Subgoal ceqG.2:
  
  Vars: D2:o, D:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_s N M D : deq M N}@
  H2:{G |- N : tm}*
  H3:{G |- M : tm}*
  H4:{G |- D : deq N M}*
  H5:{G |- D2 : aeq N M}
  
  ==================================
  exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.2>> apply symG to H5.
  
  Subgoal ceqG.2:
  
  Vars: D2:o, D:o, D1:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_s N M D : deq M N}@
  H2:{G |- N : tm}*
  H3:{G |- M : tm}*
  H4:{G |- D : deq N M}*
  H5:{G |- D2 : aeq N M}
  H6:{G |- D1 : aeq M N}
  
  ==================================
  exists D2, {G |- D2 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.2>> exists D1.
  
  Subgoal ceqG.2:
  
  Vars: D2:o, D:o, D1:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_s N M D : deq M N}@
  H2:{G |- N : tm}*
  H3:{G |- M : tm}*
  H4:{G |- D : deq N M}*
  H5:{G |- D2 : aeq N M}
  H6:{G |- D1 : aeq M N}
  
  ==================================
  {G |- D1 : aeq M N}
  
  Subgoal ceqG.3 is:
   exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.2>> search.
  
  Subgoal ceqG.3:
  
  Vars: N:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_r N : deq N N}@
  H2:{G |- N : tm}*
  
  ==================================
  exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.3>> apply reflG to H2.
  
  Subgoal ceqG.3:
  
  Vars: D:o, N:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_r N : deq N N}@
  H2:{G |- N : tm}*
  H3:{G |- D : aeq N N}
  
  ==================================
  exists D2, {G |- D2 : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.3>> exists D.
  
  Subgoal ceqG.3:
  
  Vars: D:o, N:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_r N : deq N N}@
  H2:{G |- N : tm}*
  H3:{G |- D : aeq N N}
  
  ==================================
  {G |- D : aeq N N}
  
  Subgoal ceqG.4 is:
   exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.3>> search.
  
  Subgoal ceqG.4:
  
  Vars: D:(o) -> (o) -> o, M1:(o) -> o, N1:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:
      {G |- de_l ([c27]M1 c27) ([c28]N1 c28) ([c29][c30]D c29 c30) :
        deq (lam ([c18]M1 c18)) (lam ([c21]N1 c21))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:deq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  
  ==================================
  exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.4>> weaken H4 with aeq n2 n2.
  
  Subgoal ceqG.4:
  
  Vars: D:(o) -> (o) -> o, M1:(o) -> o, N1:(o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:
      {G |- de_l ([c27]M1 c27) ([c28]N1 c28) ([c29][c30]D c29 c30) :
        deq (lam ([c18]M1 c18)) (lam ([c21]N1 c21))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:deq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H5:{G, n2:tm, n3:deq n2 n2, n4:aeq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  
  ==================================
  exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.4>> ctxpermute H5 to G,n2:tm,n4:aeq n2 n2,n3:deq n2 n2.
  
  Subgoal ceqG.4:
  
  Vars: D:(o) -> (o) -> o, M1:(o) -> o, N1:(o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:
      {G |- de_l ([c27]M1 c27) ([c28]N1 c28) ([c29][c30]D c29 c30) :
        deq (lam ([c18]M1 c18)) (lam ([c21]N1 c21))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:deq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H5:{G, n2:tm, n3:deq n2 n2, n4:aeq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H6:{G, n2:tm, n4:aeq n2 n2, n3:deq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  
  ==================================
  exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.4>> apply IH to H6 with (G = G,n1:tm,n2:aeq n1 n1,n:deq n1 n1).
  
  Subgoal ceqG.4:
  
  Vars: D2:(o) -> (o) -> (o) -> (o) -> (o) -> o, D:(o) -> (o) -> o, M1:
          (o) -> o, N1:(o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:
      {G |- de_l ([c27]M1 c27) ([c28]N1 c28) ([c29][c30]D c29 c30) :
        deq (lam ([c18]M1 c18)) (lam ([c21]N1 c21))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:deq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H5:{G, n2:tm, n3:deq n2 n2, n4:aeq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H6:{G, n2:tm, n4:aeq n2 n2, n3:deq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H7:
      {G, n1:tm, n2:aeq n1 n1, n:deq n1 n1 |- D2 n4 n3 n2 n1 n :
        aeq (M1 n1) (N1 n1)}
  
  ==================================
  exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.4>> prune H7.
  
  Subgoal ceqG.4:
  
  Vars: D2:(o) -> (o) -> (o) -> o, D:(o) -> (o) -> o, M1:(o) -> o, N1:(o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:
      {G |- de_l ([c27]M1 c27) ([c28]N1 c28) ([c29][c30]D c29 c30) :
        deq (lam ([c18]M1 c18)) (lam ([c21]N1 c21))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:deq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H5:{G, n2:tm, n3:deq n2 n2, n4:aeq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H6:{G, n2:tm, n4:aeq n2 n2, n3:deq n2 n2 |- D n2 n3 : deq (M1 n2) (N1 n2)}*
  H7:{G, n1:tm, n2:aeq n1 n1, n:deq n1 n1 |- D2 n2 n1 n : aeq (M1 n1) (N1 n1)}
  
  ==================================
  exists D2, {G |- D2 : aeq (lam ([c53]M1 c53)) (lam ([c56]N1 c56))}
  
  Subgoal ceqG.5 is:
   exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.4>> skip.
  
  Subgoal ceqG.5:
  
  Vars: D2:o, D3:o, M1:o, M2:o, N1:o, N2:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_a M1 M2 N1 N2 D2 D3 : deq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D2 : deq M1 N1}*
  H7:{G |- D3 : deq M2 N2}*
  
  ==================================
  exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.5>> apply IH to H6.
  
  Subgoal ceqG.5:
  
  Vars: D2:o, D3:o, M1:o, M2:o, N1:o, N2:o, D1:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_a M1 M2 N1 N2 D2 D3 : deq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D2 : deq M1 N1}*
  H7:{G |- D3 : deq M2 N2}*
  H8:{G |- D1 : aeq M1 N1}
  
  ==================================
  exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.5>> apply IH to H7.
  
  Subgoal ceqG.5:
  
  Vars: D4:o, D2:o, D3:o, M1:o, M2:o, N1:o, N2:o, D1:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_a M1 M2 N1 N2 D2 D3 : deq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D2 : deq M1 N1}*
  H7:{G |- D3 : deq M2 N2}*
  H8:{G |- D1 : aeq M1 N1}
  H9:{G |- D4 : aeq M2 N2}
  
  ==================================
  exists D2, {G |- D2 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.5>> exists ae_a M1 M2 N1 N2 D1 D4.
  
  Subgoal ceqG.5:
  
  Vars: D4:o, D2:o, D3:o, M1:o, M2:o, N1:o, N2:o, D1:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- de_a M1 M2 N1 N2 D2 D3 : deq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D2 : deq M1 N1}*
  H7:{G |- D3 : deq M2 N2}*
  H8:{G |- D1 : aeq M1 N1}
  H9:{G |- D4 : aeq M2 N2}
  
  ==================================
  {G |- ae_a M1 M2 N1 N2 D1 D4 : aeq (app M1 M2) (app N1 N2)}
  
  Subgoal ceqG.6 is:
   exists D2, {G |- D2 : aeq n n}
  
  ceqG.5>> search.
  
  Subgoal ceqG.6:
  
  Nominals: n2:o, n1:o, n:o
  Contexts: G{}:daG[(n:tm, n1:aeq n n, n2:deq n n)]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- n2 : deq n n}@
  
  ==================================
  exists D2, {G |- D2 : aeq n n}
  
  ceqG.6>> exists n1.
  
  Subgoal ceqG.6:
  
  Nominals: n2:o, n1:o, n:o
  Contexts: G{}:daG[(n:tm, n1:aeq n n, n2:deq n n)]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : deq M N}* => exists D2, {G |- D2 : aeq M N}
  H1:{G |- n2 : deq n n}@
  
  ==================================
  {G |- n1 : aeq n n}
  
  ceqG.6>> search.
  Proof Completed!
  
  >> Theorem seqG:
      ctx  G:daG,
        forall  M N D1, {G |- D1 : aeq M N} => exists  D2, {G |- D2 : deq M N}.
  
  Subgoal seqG:
  
  
  ==================================
  ctx G:daG,
    forall M, forall N, forall D1,
      {G |- D1 : aeq M N} => exists D2, {G |- D2 : deq M N}
  
  seqG>> induction on 1.
  
  Subgoal seqG:
  
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  
  ==================================
  ctx G:daG,
    forall M, forall N, forall D1,
      {G |- D1 : aeq M N}@ => exists D2, {G |- D2 : deq M N}
  
  seqG>> intros.
  
  Subgoal seqG:
  
  Vars: D1:o, N:o, M:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:{G |- D1 : aeq M N}@
  
  ==================================
  exists D2, {G |- D2 : deq M N}
  
  seqG>> cases H1.
  
  Subgoal seqG.1:
  
  Vars: D:(o) -> (o) -> o, M1:(o) -> o, N1:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:
      {G |- ae_l ([c12]M1 c12) ([c13]N1 c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M1 c3)) (lam ([c6]N1 c6))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M1 n2) (N1 n2)}*
  
  ==================================
  exists D2, {G |- D2 : deq (lam ([c32]M1 c32)) (lam ([c35]N1 c35))}
  
  Subgoal seqG.2 is:
   exists D2, {G |- D2 : deq (app M1 M2) (app N1 N2)}
  
  Subgoal seqG.3 is:
   exists D2, {G |- D2 : deq n n}
  
  seqG.1>> weaken H4 with deq n2 n2.
  
  Subgoal seqG.1:
  
  Vars: D:(o) -> (o) -> o, M1:(o) -> o, N1:(o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:
      {G |- ae_l ([c12]M1 c12) ([c13]N1 c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M1 c3)) (lam ([c6]N1 c6))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M1 n2) (N1 n2)}*
  H5:{G, n2:tm, n3:aeq n2 n2, n4:deq n2 n2 |- D n2 n3 : aeq (M1 n2) (N1 n2)}*
  
  ==================================
  exists D2, {G |- D2 : deq (lam ([c32]M1 c32)) (lam ([c35]N1 c35))}
  
  Subgoal seqG.2 is:
   exists D2, {G |- D2 : deq (app M1 M2) (app N1 N2)}
  
  Subgoal seqG.3 is:
   exists D2, {G |- D2 : deq n n}
  
  seqG.1>> apply IH to H5 with (G = G,n1:tm,n2:aeq n1 n1,n:deq n1 n1).
  
  Subgoal seqG.1:
  
  Vars: D2:(o) -> (o) -> (o) -> (o) -> (o) -> o, D:(o) -> (o) -> o, M1:
          (o) -> o, N1:(o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:
      {G |- ae_l ([c12]M1 c12) ([c13]N1 c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M1 c3)) (lam ([c6]N1 c6))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M1 n2) (N1 n2)}*
  H5:{G, n2:tm, n3:aeq n2 n2, n4:deq n2 n2 |- D n2 n3 : aeq (M1 n2) (N1 n2)}*
  H6:
      {G, n1:tm, n2:aeq n1 n1, n:deq n1 n1 |- D2 n4 n3 n2 n1 n :
        deq (M1 n1) (N1 n1)}
  
  ==================================
  exists D2, {G |- D2 : deq (lam ([c32]M1 c32)) (lam ([c35]N1 c35))}
  
  Subgoal seqG.2 is:
   exists D2, {G |- D2 : deq (app M1 M2) (app N1 N2)}
  
  Subgoal seqG.3 is:
   exists D2, {G |- D2 : deq n n}
  
  seqG.1>> prune H6.
  
  Subgoal seqG.1:
  
  Vars: D2:(o) -> (o) -> (o) -> o, D:(o) -> (o) -> o, M1:(o) -> o, N1:(o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:
      {G |- ae_l ([c12]M1 c12) ([c13]N1 c13) ([c14][c15]D c14 c15) :
        aeq (lam ([c3]M1 c3)) (lam ([c6]N1 c6))}@
  H2:{G, n:tm |- M1 n : tm}*
  H3:{G, n1:tm |- N1 n1 : tm}*
  H4:{G, n2:tm, n3:aeq n2 n2 |- D n2 n3 : aeq (M1 n2) (N1 n2)}*
  H5:{G, n2:tm, n3:aeq n2 n2, n4:deq n2 n2 |- D n2 n3 : aeq (M1 n2) (N1 n2)}*
  H6:{G, n1:tm, n2:aeq n1 n1, n:deq n1 n1 |- D2 n2 n1 n : deq (M1 n1) (N1 n1)}
  
  ==================================
  exists D2, {G |- D2 : deq (lam ([c32]M1 c32)) (lam ([c35]N1 c35))}
  
  Subgoal seqG.2 is:
   exists D2, {G |- D2 : deq (app M1 M2) (app N1 N2)}
  
  Subgoal seqG.3 is:
   exists D2, {G |- D2 : deq n n}
  
  seqG.1>> skip.
  
  Subgoal seqG.2:
  
  Vars: D2:o, D3:o, M1:o, M2:o, N1:o, N2:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:{G |- ae_a M1 M2 N1 N2 D2 D3 : aeq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D2 : aeq M1 N1}*
  H7:{G |- D3 : aeq M2 N2}*
  
  ==================================
  exists D2, {G |- D2 : deq (app M1 M2) (app N1 N2)}
  
  Subgoal seqG.3 is:
   exists D2, {G |- D2 : deq n n}
  
  seqG.2>> apply IH to H6.
  
  Subgoal seqG.2:
  
  Vars: D2:o, D3:o, M1:o, M2:o, N1:o, N2:o, D1:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:{G |- ae_a M1 M2 N1 N2 D2 D3 : aeq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D2 : aeq M1 N1}*
  H7:{G |- D3 : aeq M2 N2}*
  H8:{G |- D1 : deq M1 N1}
  
  ==================================
  exists D2, {G |- D2 : deq (app M1 M2) (app N1 N2)}
  
  Subgoal seqG.3 is:
   exists D2, {G |- D2 : deq n n}
  
  seqG.2>> apply IH to H7.
  
  Subgoal seqG.2:
  
  Vars: D4:o, D2:o, D3:o, M1:o, M2:o, N1:o, N2:o, D1:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:{G |- ae_a M1 M2 N1 N2 D2 D3 : aeq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D2 : aeq M1 N1}*
  H7:{G |- D3 : aeq M2 N2}*
  H8:{G |- D1 : deq M1 N1}
  H9:{G |- D4 : deq M2 N2}
  
  ==================================
  exists D2, {G |- D2 : deq (app M1 M2) (app N1 N2)}
  
  Subgoal seqG.3 is:
   exists D2, {G |- D2 : deq n n}
  
  seqG.2>> exists de_a M1 M2 N1 N2 D1 D4.
  
  Subgoal seqG.2:
  
  Vars: D4:o, D2:o, D3:o, M1:o, M2:o, N1:o, N2:o, D1:o
  Contexts: G{}:daG[]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:{G |- ae_a M1 M2 N1 N2 D2 D3 : aeq (app M1 M2) (app N1 N2)}@
  H2:{G |- M1 : tm}*
  H3:{G |- M2 : tm}*
  H4:{G |- N1 : tm}*
  H5:{G |- N2 : tm}*
  H6:{G |- D2 : aeq M1 N1}*
  H7:{G |- D3 : aeq M2 N2}*
  H8:{G |- D1 : deq M1 N1}
  H9:{G |- D4 : deq M2 N2}
  
  ==================================
  {G |- de_a M1 M2 N1 N2 D1 D4 : deq (app M1 M2) (app N1 N2)}
  
  Subgoal seqG.3 is:
   exists D2, {G |- D2 : deq n n}
  
  seqG.2>> search.
  
  Subgoal seqG.3:
  
  Nominals: n2:o, n1:o, n:o
  Contexts: G{}:daG[(n:tm, n1:aeq n n, n2:deq n n)]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:{G |- n1 : aeq n n}@
  
  ==================================
  exists D2, {G |- D2 : deq n n}
  
  seqG.3>> exists n2.
  
  Subgoal seqG.3:
  
  Nominals: n2:o, n1:o, n:o
  Contexts: G{}:daG[(n:tm, n1:aeq n n, n2:deq n n)]
  IH:
      ctx G:daG,
        forall M, forall N, forall D1,
          {G |- D1 : aeq M N}* => exists D2, {G |- D2 : deq M N}
  H1:{G |- n1 : aeq n n}@
  
  ==================================
  {G |- n2 : deq n n}
  
  seqG.3>> search.
  Proof Completed!
  
  >> Theorem substG:
      ctx  G:xaG,
        forall  M1:(o) -> o M2:(o) -> o N1 N2 D1:(o) -> (o) -> o D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq M1 x M2 x} =>
            {G |- D2 : aeq N1 N2} => exists  D3, {G |- D3 : aeq M1 N1 M2 N2}.
  
  Subgoal substG:
  
  
  ==================================
  ctx G:xaG,
    forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
      {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)} =>
          {G |- D2 : aeq N1 N2} => exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  
  substG>> induction on 1.
  
  Subgoal substG:
  
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  
  ==================================
  ctx G:xaG,
    forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
      {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}@ =>
          {G |- D2 : aeq N1 N2} => exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  
  substG>> intros.
  
  Subgoal substG:
  
  Vars: D2:o, D1:(o) -> (o) -> o, N2:o, N1:o, M2:(o) -> o, M1:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:{G, n:tm, n1:aeq n n |- D1 n n1 : aeq (M1 n) (M2 n)}@
  H2:{G |- D2 : aeq N1 N2}
  
  ==================================
  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  
  substG>> cases H1.
  
  Subgoal substG.1:
  
  Vars: D:(o) -> (o) -> (o) -> (o) -> o, M3:(o) -> (o) -> o, M4:
          (o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> ctxpermute H5 to G,n4:tm,n5:aeq n4 n4,n:tm,n1:aeq n n.
  
  Subgoal substG.1:
  
  Vars: D:(o) -> (o) -> (o) -> (o) -> o, M3:(o) -> (o) -> o, M4:
          (o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> weaken H2 with tm.
  
  Subgoal substG.1:
  
  Vars: D:(o) -> (o) -> (o) -> (o) -> o, M3:(o) -> (o) -> o, M4:
          (o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> weaken H7 with aeq n6 n6.
  
  Subgoal substG.1:
  
  Vars: D:(o) -> (o) -> (o) -> (o) -> o, M3:(o) -> (o) -> o, M4:
          (o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> apply IH to H6 H8 with (G = G,n1:tm,n:aeq n1 n1).
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, M3:(o) -> (o) -> o, M4:
          (o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:
      {G, n1:tm, n:aeq n1 n1 |- D3 n7 n6 n5 n4 n3 n2 n1 n :
        aeq (M3 N1 n1) (M4 N2 n1)}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> prune H9.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> inst H3 with n = N1.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> inst H4 with n = N2.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> strengthen H10.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> strengthen H11.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> prune H5.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  
  ==================================
  exists D3, {G |- D3 : aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> exists ae_l M3 N1 M4 N2 D3.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  
  ==================================
  {G |- ae_l (M3 N1) (M4 N2) D3 :
    aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> assert {G,n:tm |- M3 N1 n : tm}.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  
  ==================================
  {G, n:tm |- M3 N1 n : tm}
  
  Subgoal substG.1 is:
   {G |- ae_l (M3 N1) (M4 N2) D3 :
     aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> ctxpermute H10 to G,n2:tm,n1:aeq N1 N1.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  H12:{G, n2:tm, n1:aeq N1 N1 |- M3 N1 n2 : tm}
  
  ==================================
  {G, n:tm |- M3 N1 n : tm}
  
  Subgoal substG.1 is:
   {G |- ae_l (M3 N1) (M4 N2) D3 :
     aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> strengthen H12.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  H12:{G, n2:tm, n1:aeq N1 N1 |- M3 N1 n2 : tm}
  H13:{G, n2:tm |- M3 N1 n2 : tm}
  
  ==================================
  {G, n:tm |- M3 N1 n : tm}
  
  Subgoal substG.1 is:
   {G |- ae_l (M3 N1) (M4 N2) D3 :
     aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> search.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  H12:{G, n:tm |- M3 N1 n : tm}
  
  ==================================
  {G |- ae_l (M3 N1) (M4 N2) D3 :
    aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> assert {G,n:tm |- M4 N2 n : tm}.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  H12:{G, n:tm |- M3 N1 n : tm}
  
  ==================================
  {G, n:tm |- M4 N2 n : tm}
  
  Subgoal substG.1 is:
   {G |- ae_l (M3 N1) (M4 N2) D3 :
     aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> ctxpermute H11 to G,n3:tm,n1:aeq N2 N2.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  H12:{G, n:tm |- M3 N1 n : tm}
  H13:{G, n3:tm, n1:aeq N2 N2 |- M4 N2 n3 : tm}
  
  ==================================
  {G, n:tm |- M4 N2 n : tm}
  
  Subgoal substG.1 is:
   {G |- ae_l (M3 N1) (M4 N2) D3 :
     aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> strengthen H13.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  H12:{G, n:tm |- M3 N1 n : tm}
  H13:{G, n3:tm, n1:aeq N2 N2 |- M4 N2 n3 : tm}
  H14:{G, n3:tm |- M4 N2 n3 : tm}
  
  ==================================
  {G, n:tm |- M4 N2 n : tm}
  
  Subgoal substG.1 is:
   {G |- ae_l (M3 N1) (M4 N2) D3 :
     aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> search.
  
  Subgoal substG.1:
  
  Vars: D3:(o) -> (o) -> o, D:(o) -> (o) -> (o) -> (o) -> o, M3:
          (o) -> (o) -> o, M4:(o) -> (o) -> o, D2:o, N2:o, N1:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6, n7}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_l ([c12]M3 n c12) ([c13]M4 n c13) ([c14][c15]D n1 n c14 c15) :
        aeq (lam ([c3]M3 n c3)) (lam ([c6]M4 n c6))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n, n2:tm |- M3 n n2 : tm}*
  H4:{G, n:tm, n1:aeq n n, n3:tm |- M4 n n3 : tm}*
  H5:
      {G, n:tm, n1:aeq n n, n4:tm, n5:aeq n4 n4 |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H6:
      {G, n4:tm, n5:aeq n4 n4, n:tm, n1:aeq n n |- D n1 n n4 n5 :
        aeq (M3 n n4) (M4 n n4)}*
  H7:{G, n6:tm |- D2 : aeq N1 N2}
  H8:{G, n6:tm, n7:aeq n6 n6 |- D2 : aeq N1 N2}
  H9:{G, n1:tm, n:aeq n1 n1 |- D3 n1 n : aeq (M3 N1 n1) (M4 N2 n1)}
  H10:{G, n1:aeq N1 N1, n2:tm |- M3 N1 n2 : tm}
  H11:{G, n1:aeq N2 N2, n3:tm |- M4 N2 n3 : tm}
  H12:{G, n:tm |- M3 N1 n : tm}
  H13:{G, n:tm |- M4 N2 n : tm}
  
  ==================================
  {G |- ae_l (M3 N1) (M4 N2) D3 :
    aeq (lam ([c35]M3 N1 c35)) (lam ([c39]M4 N2 c39))}
  
  Subgoal substG.2 is:
   exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.1>> search.
  
  Subgoal substG.2:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, M3:(o) -> o, M4:(o) -> o, M5:
          (o) -> o, M6:(o) -> o, D2:o, N2:o, N1:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_a (M3 n) (M4 n) (M5 n) (M6 n) (D3 n1 n) (D4 n1 n) :
        aeq (app (M3 n) (M4 n)) (app (M5 n) (M6 n))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n |- M3 n : tm}*
  H4:{G, n:tm, n1:aeq n n |- M4 n : tm}*
  H5:{G, n:tm, n1:aeq n n |- M5 n : tm}*
  H6:{G, n:tm, n1:aeq n n |- M6 n : tm}*
  H7:{G, n:tm, n1:aeq n n |- D3 n1 n : aeq (M3 n) (M5 n)}*
  H8:{G, n:tm, n1:aeq n n |- D4 n1 n : aeq (M4 n) (M6 n)}*
  
  ==================================
  exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.2>> apply IH to H7 H2.
  
  Subgoal substG.2:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, M3:(o) -> o, M4:(o) -> o, M5:
          (o) -> o, M6:(o) -> o, D2:o, D1:(o) -> (o) -> o, N2:o, N1:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_a (M3 n) (M4 n) (M5 n) (M6 n) (D3 n1 n) (D4 n1 n) :
        aeq (app (M3 n) (M4 n)) (app (M5 n) (M6 n))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n |- M3 n : tm}*
  H4:{G, n:tm, n1:aeq n n |- M4 n : tm}*
  H5:{G, n:tm, n1:aeq n n |- M5 n : tm}*
  H6:{G, n:tm, n1:aeq n n |- M6 n : tm}*
  H7:{G, n:tm, n1:aeq n n |- D3 n1 n : aeq (M3 n) (M5 n)}*
  H8:{G, n:tm, n1:aeq n n |- D4 n1 n : aeq (M4 n) (M6 n)}*
  H9:{G |- D1 n1 n : aeq (M3 N1) (M5 N2)}
  
  ==================================
  exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.2>> apply IH to H8 H2.
  
  Subgoal substG.2:
  
  Vars: D5:(o) -> (o) -> o, D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, M3:
          (o) -> o, M4:(o) -> o, M5:(o) -> o, M6:(o) -> o, D2:o, D1:
          (o) -> (o) -> o, N2:o, N1:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_a (M3 n) (M4 n) (M5 n) (M6 n) (D3 n1 n) (D4 n1 n) :
        aeq (app (M3 n) (M4 n)) (app (M5 n) (M6 n))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n |- M3 n : tm}*
  H4:{G, n:tm, n1:aeq n n |- M4 n : tm}*
  H5:{G, n:tm, n1:aeq n n |- M5 n : tm}*
  H6:{G, n:tm, n1:aeq n n |- M6 n : tm}*
  H7:{G, n:tm, n1:aeq n n |- D3 n1 n : aeq (M3 n) (M5 n)}*
  H8:{G, n:tm, n1:aeq n n |- D4 n1 n : aeq (M4 n) (M6 n)}*
  H9:{G |- D1 n1 n : aeq (M3 N1) (M5 N2)}
  H10:{G |- D5 n1 n : aeq (M4 N1) (M6 N2)}
  
  ==================================
  exists D3, {G |- D3 : aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.2>> exists ae_a M3 N1 M4 N1 M5 N2 M6 N2 D1 n1 n D5 n1 n.
  
  Subgoal substG.2:
  
  Vars: D5:(o) -> (o) -> o, D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, M3:
          (o) -> o, M4:(o) -> o, M5:(o) -> o, M6:(o) -> o, D2:o, D1:
          (o) -> (o) -> o, N2:o, N1:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:
      {G, n:tm, n1:aeq n n |- 
        ae_a (M3 n) (M4 n) (M5 n) (M6 n) (D3 n1 n) (D4 n1 n) :
        aeq (app (M3 n) (M4 n)) (app (M5 n) (M6 n))}@
  H2:{G |- D2 : aeq N1 N2}
  H3:{G, n:tm, n1:aeq n n |- M3 n : tm}*
  H4:{G, n:tm, n1:aeq n n |- M4 n : tm}*
  H5:{G, n:tm, n1:aeq n n |- M5 n : tm}*
  H6:{G, n:tm, n1:aeq n n |- M6 n : tm}*
  H7:{G, n:tm, n1:aeq n n |- D3 n1 n : aeq (M3 n) (M5 n)}*
  H8:{G, n:tm, n1:aeq n n |- D4 n1 n : aeq (M4 n) (M6 n)}*
  H9:{G |- D1 n1 n : aeq (M3 N1) (M5 N2)}
  H10:{G |- D5 n1 n : aeq (M4 N1) (M6 N2)}
  
  ==================================
  {G |- ae_a (M3 N1) (M4 N1) (M5 N2) (M6 N2) (D1 n1 n) (D5 n1 n) :
    aeq (app (M3 N1) (M4 N1)) (app (M5 N2) (M6 N2))}
  
  Subgoal substG.3 is:
   exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.2>> search.
  
  Subgoal substG.3:
  
  Vars: D2:o, N2:o, N1:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:{G, n:tm, n1:aeq n n |- n1 : aeq n n}@
  H2:{G |- D2 : aeq N1 N2}
  
  ==================================
  exists D3, {G |- D3 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.3>> exists D2.
  
  Subgoal substG.3:
  
  Vars: D2:o, N2:o, N1:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:xaG[]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:{G, n:tm, n1:aeq n n |- n1 : aeq n n}@
  H2:{G |- D2 : aeq N1 N2}
  
  ==================================
  {G |- D2 : aeq N1 N2}
  
  Subgoal substG.4 is:
   exists D3, {G |- D3 : aeq n2 n2}
  
  substG.3>> search.
  
  Subgoal substG.4:
  
  Vars: D2:(o) -> (o) -> o, N2:(o) -> (o) -> o, N1:(o) -> (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1}:xaG[(n2:tm, n3:aeq n2 n2)]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:{G, n:tm, n1:aeq n n |- n3 : aeq n2 n2}@
  H2:{G |- D2 n2 n3 : aeq (N1 n2 n3) (N2 n2 n3)}
  
  ==================================
  exists D3, {G |- D3 : aeq n2 n2}
  
  substG.4>> exists n3.
  
  Subgoal substG.4:
  
  Vars: D2:(o) -> (o) -> o, N2:(o) -> (o) -> o, N1:(o) -> (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1}:xaG[(n2:tm, n3:aeq n2 n2)]
  IH:
      ctx G:xaG,
        forall M1, forall M2, forall N1, forall N2, forall D1, forall D2,
          {G |- [x][y]D1 x y : {x:tm}{y:aeq x x}aeq (M1 x) (M2 x)}* =>
              {G |- D2 : aeq N1 N2} =>
                  exists D3, {G |- D3 : aeq (M1 N1) (M2 N2)}
  H1:{G, n:tm, n1:aeq n n |- n3 : aeq n2 n2}@
  H2:{G |- D2 n2 n3 : aeq (N1 n2 n3) (N2 n2 n3)}
  
  ==================================
  {G |- n3 : aeq n2 n2}
  
  substG.4>> search.
  Proof Completed!
  
  >> Theorem reflR:
      ctx  G1:xG,
        ctx  G2:xaG,
          forall  M, {G1 |- M : tm} => exists  D, {G2 |- D : aeq M M}.
  
  Subgoal reflR:
  
  
  ==================================
  ctx G1:xG, ctx G2:xaG,
    forall M, {G1 |- M : tm} => exists D, {G2 |- D : aeq M M}
  
  reflR>> induction on 1.
  
  Subgoal reflR:
  
  IH:
      ctx G1:xG, ctx G2:xaG,
        forall M, {G1 |- M : tm}* => exists D, {G2 |- D : aeq M M}
  
  ==================================
  ctx G1:xG, ctx G2:xaG,
    forall M, {G1 |- M : tm}@ => exists D, {G2 |- D : aeq M M}
  
  reflR>> intros.
  
  Subgoal reflR:
  
  Vars: M:o
  Contexts: G2{}:xaG[], G1{}:xG[]
  IH:
      ctx G1:xG, ctx G2:xaG,
        forall M, {G1 |- M : tm}* => exists D, {G2 |- D : aeq M M}
  H1:{G1 |- M : tm}@
  
  ==================================
  exists D, {G2 |- D : aeq M M}
  
  reflR>> cases H1.
  
  Subgoal reflR.1:
  
  Vars: M1:o, M2:o
  Contexts: G2{}:xaG[], G1{}:xG[]
  IH:
      ctx G1:xG, ctx G2:xaG,
        forall M, {G1 |- M : tm}* => exists D, {G2 |- D : aeq M M}
  H2:{G1 |- M1 : tm}*
  H3:{G1 |- M2 : tm}*
  
  ==================================
  exists D, {G2 |- D : aeq (app M1 M2) (app M1 M2)}
  
  Subgoal reflR.2 is:
   exists D, {G2 |- D : aeq (lam ([c13]M1 c13)) (lam ([c16]M1 c16))}
  
  Subgoal reflR.3 is:
   exists D, {G2 |- D : aeq n n}
  
  reflR.1>> apply IH to H2.
  Error: Unable to find instantiation for context variable:
   G4
   in formula:
   exists D, {G4 |- D : aeq M1 M1}
  [1]
