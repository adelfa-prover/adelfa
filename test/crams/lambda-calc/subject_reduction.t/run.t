Since these tests share a single specification file, group them here
  $ adelfa -i generalized.ath
  Welcome!
  >> Specification generalized.lf.
  
  >> Schema c := {T}(x:tm,y:of x T).
  
  >> Theorem subject_reduction:
      ctx  Gamma:c,
        forall  M1 M2 T D1 D2,
          {Gamma |- D1 : step M1 M2} =>
            {Gamma |- D2 : of M1 T} => exists  D3, {Gamma |- D3 : of M2 T}.
  
  Subgoal subject_reduction:
  
  
  ==================================
  ctx Gamma:c.
    forall M1, forall M2, forall T, forall D1, forall D2,
      {Gamma |- D1 : step M1 M2} =>
          {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction>> induction on 1.
  
  Subgoal subject_reduction:
  
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  
  ==================================
  ctx Gamma:c.
    forall M1, forall M2, forall T, forall D1, forall D2,
      {Gamma |- D1 : step M1 M2}@ =>
          {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction>> intros.
  
  Subgoal subject_reduction:
  
  Vars: D2:o, D1:o, T:o, M2:o, M1:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : step M1 M2}@
  H2:{Gamma |- D2 : of M1 T}
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction>> cases H1.
  
  Subgoal subject_reduction.1:
  
  Vars: D:(o) -> (o) -> o, R1:(o) -> o, T1:o, R2:(o) -> o, D2:o, T:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H2:{Gamma |- D2 : of (lam T1 R1) T}
  H3:{Gamma |- T1 : ty}*
  H4:{Gamma, n:tm |- R1 n : tm}*
  H5:{Gamma, n1:tm |- R2 n1 : tm}*
  H6:{Gamma, n2:tm, n3:of n2 T1 |- D n2 n3 : step (R1 n2) (R2 n2)}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (lam T1 R2) T}
  
  Subgoal subject_reduction.2 is:
   exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.1>> cases H2.
  
  Subgoal subject_reduction.1:
  
  Vars: D3:(o) -> (o) -> o, T2:o, D:(o) -> (o) -> o, R1:(o) -> o, T1:o, R2:
          (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- T1 : ty}*
  H4:{Gamma, n:tm |- R1 n : tm}*
  H5:{Gamma, n1:tm |- R2 n1 : tm}*
  H6:{Gamma, n2:tm, n3:of n2 T1 |- D n2 n3 : step (R1 n2) (R2 n2)}*
  H7:{Gamma, n4:tm |- R1 n4 : tm}
  H8:{Gamma |- T1 : ty}
  H9:{Gamma |- T2 : ty}
  H10:{Gamma, n5:tm, n6:of n5 T1 |- D3 n5 n6 : of (R1 n5) T2}
  
  ==================================
  exists D3, {Gamma |- D3 : of (lam T1 R2) (arr T1 T2)}
  
  Subgoal subject_reduction.2 is:
   exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.1>> apply IH to H6 H10.
  
  Subgoal subject_reduction.1:
  
  Vars: D3:(o) -> (o) -> o, T2:o, D:(o) -> (o) -> o, R1:(o) -> o, T1:o, R2:
          (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- T1 : ty}*
  H4:{Gamma, n:tm |- R1 n : tm}*
  H5:{Gamma, n1:tm |- R2 n1 : tm}*
  H6:{Gamma, n2:tm, n3:of n2 T1 |- D n2 n3 : step (R1 n2) (R2 n2)}*
  H7:{Gamma, n4:tm |- R1 n4 : tm}
  H8:{Gamma |- T1 : ty}
  H9:{Gamma |- T2 : ty}
  H10:{Gamma, n5:tm, n6:of n5 T1 |- D3 n5 n6 : of (R1 n5) T2}
  H11:{Gamma, n1:tm, n:of n1 T1 |- D1 n6 n5 n4 n3 n2 n1 n : of (R2 n1) T2}
  
  ==================================
  exists D3, {Gamma |- D3 : of (lam T1 R2) (arr T1 T2)}
  
  Subgoal subject_reduction.2 is:
   exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.1>> prune H11.
  
  Subgoal subject_reduction.1:
  
  Vars: D3:(o) -> (o) -> o, T2:o, D:(o) -> (o) -> o, R1:(o) -> o, T1:o, R2:
          (o) -> o, D1:(o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- T1 : ty}*
  H4:{Gamma, n:tm |- R1 n : tm}*
  H5:{Gamma, n1:tm |- R2 n1 : tm}*
  H6:{Gamma, n2:tm, n3:of n2 T1 |- D n2 n3 : step (R1 n2) (R2 n2)}*
  H7:{Gamma, n4:tm |- R1 n4 : tm}
  H8:{Gamma |- T1 : ty}
  H9:{Gamma |- T2 : ty}
  H10:{Gamma, n5:tm, n6:of n5 T1 |- D3 n5 n6 : of (R1 n5) T2}
  H11:{Gamma, n1:tm, n:of n1 T1 |- D1 n1 n : of (R2 n1) T2}
  
  ==================================
  exists D3, {Gamma |- D3 : of (lam T1 R2) (arr T1 T2)}
  
  Subgoal subject_reduction.2 is:
   exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.1>> exists of_lam R2 T1 T2 ([x][x1]D1 x x1).
  
  Subgoal subject_reduction.1:
  
  Vars: D3:(o) -> (o) -> o, T2:o, D:(o) -> (o) -> o, R1:(o) -> o, T1:o, R2:
          (o) -> o, D1:(o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- T1 : ty}*
  H4:{Gamma, n:tm |- R1 n : tm}*
  H5:{Gamma, n1:tm |- R2 n1 : tm}*
  H6:{Gamma, n2:tm, n3:of n2 T1 |- D n2 n3 : step (R1 n2) (R2 n2)}*
  H7:{Gamma, n4:tm |- R1 n4 : tm}
  H8:{Gamma |- T1 : ty}
  H9:{Gamma |- T2 : ty}
  H10:{Gamma, n5:tm, n6:of n5 T1 |- D3 n5 n6 : of (R1 n5) T2}
  H11:{Gamma, n1:tm, n:of n1 T1 |- D1 n1 n : of (R2 n1) T2}
  
  ==================================
  {Gamma |- of_lam R2 T1 T2 ([x][x1]D1 x x1) : of (lam T1 R2) (arr T1 T2)}
  
  Subgoal subject_reduction.2 is:
   exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.1>> search.
  
  Subgoal subject_reduction.2:
  
  Vars: T1:o, R:(o) -> o, N:o, D2:o, T:o
  Nominals: n:o
  Contexts: Gamma{n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H2:{Gamma |- D2 : of (app (lam T1 R) N) T}
  H3:{Gamma |- T1 : ty}*
  H4:{Gamma, n:tm |- R n : tm}*
  H5:{Gamma |- N : tm}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.2>> cases H2.
  
  Subgoal subject_reduction.2:
  
  Vars: D3:o, D4:o, D5:o, T1:o, R:(o) -> o, N:o, T:o
  Nominals: n:o
  Contexts: Gamma{n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- T1 : ty}*
  H4:{Gamma, n:tm |- R n : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- lam T1 R : tm}
  H7:{Gamma |- N : tm}
  H8:{Gamma |- T : ty}
  H9:{Gamma |- D3 : ty}
  H10:{Gamma |- D4 : of (lam T1 R) (arr D3 T)}
  H11:{Gamma |- D5 : of N D3}
  
  ==================================
  exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.2>> cases H10.
  
  Subgoal subject_reduction.2:
  
  Vars: D6:(o) -> (o) -> o, D3:o, D5:o, R:(o) -> o, N:o, T:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- D3 : ty}*
  H4:{Gamma, n:tm |- R n : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- lam D3 R : tm}
  H7:{Gamma |- N : tm}
  H8:{Gamma |- T : ty}
  H9:{Gamma |- D3 : ty}
  H11:{Gamma |- D5 : of N D3}
  H12:{Gamma, n1:tm |- R n1 : tm}
  H13:{Gamma |- D3 : ty}
  H14:{Gamma |- T : ty}
  H15:{Gamma, n2:tm, n3:of n2 D3 |- D6 n2 n3 : of (R n2) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.2>> inst H15 with n2 = N.
  
  Subgoal subject_reduction.2:
  
  Vars: D6:(o) -> (o) -> o, D3:o, D5:o, R:(o) -> o, N:o, T:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- D3 : ty}*
  H4:{Gamma, n:tm |- R n : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- lam D3 R : tm}
  H7:{Gamma |- N : tm}
  H8:{Gamma |- T : ty}
  H9:{Gamma |- D3 : ty}
  H11:{Gamma |- D5 : of N D3}
  H12:{Gamma, n1:tm |- R n1 : tm}
  H13:{Gamma |- D3 : ty}
  H14:{Gamma |- T : ty}
  H15:{Gamma, n2:tm, n3:of n2 D3 |- D6 n2 n3 : of (R n2) T}
  H16:{Gamma, n3:of N D3 |- D6 N n3 : of (R N) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.2>> inst H16 with n3 = D5.
  
  Subgoal subject_reduction.2:
  
  Vars: D6:(o) -> (o) -> o, D3:o, D5:o, R:(o) -> o, N:o, T:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- D3 : ty}*
  H4:{Gamma, n:tm |- R n : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- lam D3 R : tm}
  H7:{Gamma |- N : tm}
  H8:{Gamma |- T : ty}
  H9:{Gamma |- D3 : ty}
  H11:{Gamma |- D5 : of N D3}
  H12:{Gamma, n1:tm |- R n1 : tm}
  H13:{Gamma |- D3 : ty}
  H14:{Gamma |- T : ty}
  H15:{Gamma, n2:tm, n3:of n2 D3 |- D6 n2 n3 : of (R n2) T}
  H16:{Gamma, n3:of N D3 |- D6 N n3 : of (R N) T}
  H17:{Gamma |- D6 N D5 : of (R N) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.2>> exists D6 N D5.
  
  Subgoal subject_reduction.2:
  
  Vars: D6:(o) -> (o) -> o, D3:o, D5:o, R:(o) -> o, N:o, T:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- D3 : ty}*
  H4:{Gamma, n:tm |- R n : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- lam D3 R : tm}
  H7:{Gamma |- N : tm}
  H8:{Gamma |- T : ty}
  H9:{Gamma |- D3 : ty}
  H11:{Gamma |- D5 : of N D3}
  H12:{Gamma, n1:tm |- R n1 : tm}
  H13:{Gamma |- D3 : ty}
  H14:{Gamma |- T : ty}
  H15:{Gamma, n2:tm, n3:of n2 D3 |- D6 n2 n3 : of (R n2) T}
  H16:{Gamma, n3:of N D3 |- D6 N n3 : of (R N) T}
  H17:{Gamma |- D6 N D5 : of (R N) T}
  
  ==================================
  {Gamma |- D6 N D5 : of (R N) T}
  
  Subgoal subject_reduction.3 is:
   exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.2>> search.
  
  Subgoal subject_reduction.3:
  
  Vars: D:o, N1:o, M:o, N2:o, D2:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H2:{Gamma |- D2 : of (app M N1) T}
  H3:{Gamma |- M : tm}*
  H4:{Gamma |- N1 : tm}*
  H5:{Gamma |- N2 : tm}*
  H6:{Gamma |- D : step N1 N2}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.3>> cases H2.
  
  Subgoal subject_reduction.3:
  
  Vars: U:o, a1:o, a2:o, D:o, N1:o, M:o, N2:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- M : tm}*
  H4:{Gamma |- N1 : tm}*
  H5:{Gamma |- N2 : tm}*
  H6:{Gamma |- D : step N1 N2}*
  H7:{Gamma |- M : tm}
  H8:{Gamma |- N1 : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M (arr U T)}
  H12:{Gamma |- a2 : of N1 U}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.3>> apply IH to H6 H12.
  
  Subgoal subject_reduction.3:
  
  Vars: D3:o, U:o, a1:o, a2:o, D:o, N1:o, M:o, N2:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- M : tm}*
  H4:{Gamma |- N1 : tm}*
  H5:{Gamma |- N2 : tm}*
  H6:{Gamma |- D : step N1 N2}*
  H7:{Gamma |- M : tm}
  H8:{Gamma |- N1 : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M (arr U T)}
  H12:{Gamma |- a2 : of N1 U}
  H13:{Gamma |- D3 : of N2 U}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.3>> exists of_app M N2 T U a1 D3.
  
  Subgoal subject_reduction.3:
  
  Vars: D3:o, U:o, a1:o, a2:o, D:o, N1:o, M:o, N2:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- M : tm}*
  H4:{Gamma |- N1 : tm}*
  H5:{Gamma |- N2 : tm}*
  H6:{Gamma |- D : step N1 N2}*
  H7:{Gamma |- M : tm}
  H8:{Gamma |- N1 : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M (arr U T)}
  H12:{Gamma |- a2 : of N1 U}
  H13:{Gamma |- D3 : of N2 U}
  
  ==================================
  {Gamma |- of_app M N2 T U a1 D3 : of (app M N2) T}
  
  Subgoal subject_reduction.4 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.3>> search.
  
  Subgoal subject_reduction.4:
  
  Vars: D:o, M3:o, M4:o, N:o, D2:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H2:{Gamma |- D2 : of (app M3 N) T}
  H3:{Gamma |- M3 : tm}*
  H4:{Gamma |- M4 : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- D : step M3 M4}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.4>> cases H2.
  
  Subgoal subject_reduction.4:
  
  Vars: U:o, a1:o, a2:o, D:o, M3:o, M4:o, N:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- M3 : tm}*
  H4:{Gamma |- M4 : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- D : step M3 M4}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.4>> apply IH to H6 H11.
  
  Subgoal subject_reduction.4:
  
  Vars: D3:o, U:o, a1:o, a2:o, D:o, M3:o, M4:o, N:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- M3 : tm}*
  H4:{Gamma |- M4 : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- D : step M3 M4}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  H13:{Gamma |- D3 : of M4 (arr U T)}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction.4>> exists of_app M4 N T U D3 a2.
  
  Subgoal subject_reduction.4:
  
  Vars: D3:o, U:o, a1:o, a2:o, D:o, M3:o, M4:o, N:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : step M1 M2}* =>
              {Gamma |- D2 : of M1 T} => exists D3, {Gamma |- D3 : of M2 T}
  H3:{Gamma |- M3 : tm}*
  H4:{Gamma |- M4 : tm}*
  H5:{Gamma |- N : tm}*
  H6:{Gamma |- D : step M3 M4}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  H13:{Gamma |- D3 : of M4 (arr U T)}
  
  ==================================
  {Gamma |- of_app M4 N T U D3 a2 : of (app M4 N) T}
  
  subject_reduction.4>> search.
  Proof Completed!
  
  >> Goodbye!

  $ adelfa -i small_step.ath
  Welcome!
  >> Specification reduce.lf.
  
  >> Schema c := {T}(x:tm,y:of x T).
  
  >> Theorem subject_reduction_wsscbv:
      ctx  Gamma:c,
        forall  M1 M2 T D1 D2,
          {Gamma |- D1 : of M1 T} =>
            {D2 : sscbv M1 M2} => exists  D3, {Gamma |- D3 : of M2 T}.
  
  Subgoal subject_reduction_wsscbv:
  
  
  ==================================
  ctx Gamma:c.
    forall M1, forall M2, forall T, forall D1, forall D2,
      {Gamma |- D1 : of M1 T} =>
          {D2 : sscbv M1 M2} => exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction_wsscbv>> induction on 2.
  
  Subgoal subject_reduction_wsscbv:
  
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  
  ==================================
  ctx Gamma:c.
    forall M1, forall M2, forall T, forall D1, forall D2,
      {Gamma |- D1 : of M1 T} =>
          {D2 : sscbv M1 M2}@ => exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction_wsscbv>> intros.
  
  Subgoal subject_reduction_wsscbv:
  
  Vars: D2:o, D1:o, T:o, M2:o, M1:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of M1 T}
  H2:{D2 : sscbv M1 M2}@
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction_wsscbv>> cases H2.
  
  Subgoal subject_reduction_wsscbv.1:
  
  Vars: T1:o, R1:(o) -> o, T2:o, R2:(o) -> o, D1:o, T:o
  Nominals: n1:o, n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of (app (lam T1 R1) (lam T2 R2)) T}
  H3:{n:tm |- R1 n : tm}*
  H4:{n1:tm |- R2 n1 : tm}*
  H5:{T1 : ty}*
  H6:{T2 : ty}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (R1 (lam T2 R2)) T}
  
  Subgoal subject_reduction_wsscbv.2 is:
   exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.1>> cases H1.
  
  Subgoal subject_reduction_wsscbv.1:
  
  Vars: D3:o, D4:o, D5:o, T1:o, R1:(o) -> o, T2:o, R2:(o) -> o, T:o
  Nominals: n1:o, n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R1 n : tm}*
  H4:{n1:tm |- R2 n1 : tm}*
  H5:{T1 : ty}*
  H6:{T2 : ty}*
  H7:{Gamma |- lam T1 R1 : tm}
  H8:{Gamma |- lam T2 R2 : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- D3 : ty}
  H11:{Gamma |- D4 : of (lam T1 R1) (arr D3 T)}
  H12:{Gamma |- D5 : of (lam T2 R2) D3}
  
  ==================================
  exists D3, {Gamma |- D3 : of (R1 (lam T2 R2)) T}
  
  Subgoal subject_reduction_wsscbv.2 is:
   exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.1>> cases H11.
  
  Subgoal subject_reduction_wsscbv.1:
  
  Vars: D6:(o) -> (o) -> o, D3:o, D5:o, R1:(o) -> o, T2:o, R2:(o) -> o, T:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n4, n3, n2}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R1 n : tm}*
  H4:{n1:tm |- R2 n1 : tm}*
  H5:{D3 : ty}*
  H6:{T2 : ty}*
  H7:{Gamma |- lam D3 R1 : tm}
  H8:{Gamma |- lam T2 R2 : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- D3 : ty}
  H12:{Gamma |- D5 : of (lam T2 R2) D3}
  H13:{Gamma, n2:tm |- R1 n2 : tm}
  H14:{Gamma |- D3 : ty}
  H15:{Gamma |- T : ty}
  H16:{Gamma, n3:tm, n4:of n3 D3 |- D6 n3 n4 : of (R1 n3) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of (R1 (lam T2 R2)) T}
  
  Subgoal subject_reduction_wsscbv.2 is:
   exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.1>> inst H16 with n3 = lam T2 R2.
  
  Subgoal subject_reduction_wsscbv.1:
  
  Vars: D6:(o) -> (o) -> o, D3:o, D5:o, R1:(o) -> o, T2:o, R2:(o) -> o, T:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n4, n3, n2}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R1 n : tm}*
  H4:{n1:tm |- R2 n1 : tm}*
  H5:{D3 : ty}*
  H6:{T2 : ty}*
  H7:{Gamma |- lam D3 R1 : tm}
  H8:{Gamma |- lam T2 R2 : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- D3 : ty}
  H12:{Gamma |- D5 : of (lam T2 R2) D3}
  H13:{Gamma, n2:tm |- R1 n2 : tm}
  H14:{Gamma |- D3 : ty}
  H15:{Gamma |- T : ty}
  H16:{Gamma, n3:tm, n4:of n3 D3 |- D6 n3 n4 : of (R1 n3) T}
  H17:
      {Gamma, n4:of (lam T2 R2) D3 |- D6 (lam T2 R2) n4 :
        of (R1 (lam T2 R2)) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of (R1 (lam T2 R2)) T}
  
  Subgoal subject_reduction_wsscbv.2 is:
   exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.1>> inst H17 with n4 = D5.
  
  Subgoal subject_reduction_wsscbv.1:
  
  Vars: D6:(o) -> (o) -> o, D3:o, D5:o, R1:(o) -> o, T2:o, R2:(o) -> o, T:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n4, n3, n2}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R1 n : tm}*
  H4:{n1:tm |- R2 n1 : tm}*
  H5:{D3 : ty}*
  H6:{T2 : ty}*
  H7:{Gamma |- lam D3 R1 : tm}
  H8:{Gamma |- lam T2 R2 : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- D3 : ty}
  H12:{Gamma |- D5 : of (lam T2 R2) D3}
  H13:{Gamma, n2:tm |- R1 n2 : tm}
  H14:{Gamma |- D3 : ty}
  H15:{Gamma |- T : ty}
  H16:{Gamma, n3:tm, n4:of n3 D3 |- D6 n3 n4 : of (R1 n3) T}
  H17:
      {Gamma, n4:of (lam T2 R2) D3 |- D6 (lam T2 R2) n4 :
        of (R1 (lam T2 R2)) T}
  H18:{Gamma |- D6 (lam T2 R2) D5 : of (R1 (lam T2 R2)) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of (R1 (lam T2 R2)) T}
  
  Subgoal subject_reduction_wsscbv.2 is:
   exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.1>> exists D6 lam T2 R2 D5.
  
  Subgoal subject_reduction_wsscbv.1:
  
  Vars: D6:(o) -> (o) -> o, D3:o, D5:o, R1:(o) -> o, T2:o, R2:(o) -> o, T:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n4, n3, n2}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R1 n : tm}*
  H4:{n1:tm |- R2 n1 : tm}*
  H5:{D3 : ty}*
  H6:{T2 : ty}*
  H7:{Gamma |- lam D3 R1 : tm}
  H8:{Gamma |- lam T2 R2 : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- D3 : ty}
  H12:{Gamma |- D5 : of (lam T2 R2) D3}
  H13:{Gamma, n2:tm |- R1 n2 : tm}
  H14:{Gamma |- D3 : ty}
  H15:{Gamma |- T : ty}
  H16:{Gamma, n3:tm, n4:of n3 D3 |- D6 n3 n4 : of (R1 n3) T}
  H17:
      {Gamma, n4:of (lam T2 R2) D3 |- D6 (lam T2 R2) n4 :
        of (R1 (lam T2 R2)) T}
  H18:{Gamma |- D6 (lam T2 R2) D5 : of (R1 (lam T2 R2)) T}
  
  ==================================
  {Gamma |- D6 (lam T2 R2) D5 : of (R1 (lam T2 R2)) T}
  
  Subgoal subject_reduction_wsscbv.2 is:
   exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.1>> search.
  
  Subgoal subject_reduction_wsscbv.2:
  
  Vars: D3:o, M3:o, T1:o, R:(o) -> o, M4:o, D1:o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of (app (lam T1 R) M3) T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  H5:{M3 : tm}*
  H6:{M4 : tm}*
  H7:{D3 : sscbv M3 M4}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2>> cases H1.
  
  Subgoal subject_reduction_wsscbv.2:
  
  Vars: D4:o, D5:o, D6:o, D3:o, M3:o, T1:o, R:(o) -> o, M4:o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  H5:{M3 : tm}*
  H6:{M4 : tm}*
  H7:{D3 : sscbv M3 M4}*
  H8:{Gamma |- lam T1 R : tm}
  H9:{Gamma |- M3 : tm}
  H10:{Gamma |- T : ty}
  H11:{Gamma |- D4 : ty}
  H12:{Gamma |- D5 : of (lam T1 R) (arr D4 T)}
  H13:{Gamma |- D6 : of M3 D4}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2>> apply IH to H13 H7.
  
  Subgoal subject_reduction_wsscbv.2:
  
  Vars: D4:o, D5:o, D6:o, D3:o, M3:o, T1:o, R:(o) -> o, M4:o, D1:(o) -> o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  H5:{M3 : tm}*
  H6:{M4 : tm}*
  H7:{D3 : sscbv M3 M4}*
  H8:{Gamma |- lam T1 R : tm}
  H9:{Gamma |- M3 : tm}
  H10:{Gamma |- T : ty}
  H11:{Gamma |- D4 : ty}
  H12:{Gamma |- D5 : of (lam T1 R) (arr D4 T)}
  H13:{Gamma |- D6 : of M3 D4}
  H14:{Gamma |- D1 n : of M4 D4}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2>> prune H14.
  
  Subgoal subject_reduction_wsscbv.2:
  
  Vars: D4:o, D5:o, D6:o, D3:o, M3:o, T1:o, R:(o) -> o, M4:o, D1:(o) -> o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  H5:{M3 : tm}*
  H6:{M4 : tm}*
  H7:{D3 : sscbv M3 M4}*
  H8:{Gamma |- lam T1 R : tm}
  H9:{Gamma |- M3 : tm}
  H10:{Gamma |- T : ty}
  H11:{Gamma |- D4 : ty}
  H12:{Gamma |- D5 : of (lam T1 R) (arr D4 T)}
  H13:{Gamma |- D6 : of M3 D4}
  H14:{Gamma |- D1 n : of M4 D4}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2>> exists of_app lam T1 R M4 T D4 D5 D1 n.
  
  Subgoal subject_reduction_wsscbv.2:
  
  Vars: D4:o, D5:o, D6:o, D3:o, M3:o, T1:o, R:(o) -> o, M4:o, D1:(o) -> o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  H5:{M3 : tm}*
  H6:{M4 : tm}*
  H7:{D3 : sscbv M3 M4}*
  H8:{Gamma |- lam T1 R : tm}
  H9:{Gamma |- M3 : tm}
  H10:{Gamma |- T : ty}
  H11:{Gamma |- D4 : ty}
  H12:{Gamma |- D5 : of (lam T1 R) (arr D4 T)}
  H13:{Gamma |- D6 : of M3 D4}
  H14:{Gamma |- D1 n : of M4 D4}
  
  ==================================
  {Gamma |- of_app (lam T1 R) M4 T D4 D5 (D1 n) : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2>> assert {Gamma |- M4 : tm}.
  
  Subgoal subject_reduction_wsscbv.2:
  
  Vars: D4:o, D5:o, D6:o, D3:o, M3:o, T1:o, R:(o) -> o, M4:o, D1:(o) -> o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  H5:{M3 : tm}*
  H6:{M4 : tm}*
  H7:{D3 : sscbv M3 M4}*
  H8:{Gamma |- lam T1 R : tm}
  H9:{Gamma |- M3 : tm}
  H10:{Gamma |- T : ty}
  H11:{Gamma |- D4 : ty}
  H12:{Gamma |- D5 : of (lam T1 R) (arr D4 T)}
  H13:{Gamma |- D6 : of M3 D4}
  H14:{Gamma |- D1 n : of M4 D4}
  H15:{Gamma |- M4 : tm}
  
  ==================================
  {Gamma |- of_app (lam T1 R) M4 T D4 D5 (D1 n) : of (app (lam T1 R) M4) T}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2>> cases H14.
  
  Subgoal subject_reduction_wsscbv.2.1:
  
  Vars: a1:(o) -> (o) -> (o) -> o, M6:(o) -> o, M5:o, D7:o, D5:o, D6:o, D3:o,
          M3:o, T1:o, R:(o) -> o, T:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  H5:{M3 : tm}*
  H6:{lam M5 M6 : tm}*
  H7:{D3 : sscbv M3 (lam M5 M6)}*
  H8:{Gamma |- lam T1 R : tm}
  H9:{Gamma |- M3 : tm}
  H10:{Gamma |- T : ty}
  H11:{Gamma |- arr M5 D7 : ty}
  H12:{Gamma |- D5 : of (lam T1 R) (arr (arr M5 D7) T)}
  H13:{Gamma |- D6 : of M3 (arr M5 D7)}
  H15:{Gamma |- lam M5 M6 : tm}
  H16:{Gamma, n1:tm |- M6 n1 : tm}
  H17:{Gamma |- M5 : ty}
  H18:{Gamma |- D7 : ty}
  H19:{Gamma, n2:tm, n3:of n2 M5 |- a1 n n2 n3 : of (M6 n2) D7}
  
  ==================================
  {Gamma |- 
    of_app (lam T1 R) (lam M5 M6) T (arr M5 D7) D5 (of_lam M6 M5 D7 (a1 n)) :
    of (app (lam T1 R) (lam M5 M6)) T}
  
  Subgoal subject_reduction_wsscbv.2.2 is:
   {Gamma |- 
     of_app (lam T1 R) (app M5 M6) T D4 D5
       (of_app M5 M6 D4 (U n) (a1 n) (a2 n))
     : of (app (lam T1 R) (app M5 M6)) T}
  
  Subgoal subject_reduction_wsscbv.2.3 is:
   {Gamma |- 
     of_app (lam (T1 n1 n2) (R n1 n2)) n1 (T n1 n2) (D4 n1 n2) (D5 n1 n2) n2 :
     of (app (lam (T1 n1 n2) (R n1 n2)) n1) (T n1 n2)}
  
  Subgoal subject_reduction_wsscbv.2.4 is:
   {Gamma |- of_app (lam (T1 n1) (R n1)) n1 (T n1) (D4 n1) (D5 n1) n :
     of (app (lam (T1 n1) (R n1)) n1) (T n1)}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2.1>> search.
  
  Subgoal subject_reduction_wsscbv.2.2:
  
  Vars: U:(o) -> o, a1:(o) -> o, a2:(o) -> o, M5:o, M6:o, D4:o, D5:o, D6:o, D3:
          o, M3:o, T1:o, R:(o) -> o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  H5:{M3 : tm}*
  H6:{app M5 M6 : tm}*
  H7:{D3 : sscbv M3 (app M5 M6)}*
  H8:{Gamma |- lam T1 R : tm}
  H9:{Gamma |- M3 : tm}
  H10:{Gamma |- T : ty}
  H11:{Gamma |- D4 : ty}
  H12:{Gamma |- D5 : of (lam T1 R) (arr D4 T)}
  H13:{Gamma |- D6 : of M3 D4}
  H15:{Gamma |- app M5 M6 : tm}
  H16:{Gamma |- M5 : tm}
  H17:{Gamma |- M6 : tm}
  H18:{Gamma |- D4 : ty}
  H19:{Gamma |- U n : ty}
  H20:{Gamma |- a1 n : of M5 (arr (U n) D4)}
  H21:{Gamma |- a2 n : of M6 (U n)}
  
  ==================================
  {Gamma |- 
    of_app (lam T1 R) (app M5 M6) T D4 D5 (of_app M5 M6 D4 (U n) (a1 n) (a2 n))
    : of (app (lam T1 R) (app M5 M6)) T}
  
  Subgoal subject_reduction_wsscbv.2.3 is:
   {Gamma |- 
     of_app (lam (T1 n1 n2) (R n1 n2)) n1 (T n1 n2) (D4 n1 n2) (D5 n1 n2) n2 :
     of (app (lam (T1 n1 n2) (R n1 n2)) n1) (T n1 n2)}
  
  Subgoal subject_reduction_wsscbv.2.4 is:
   {Gamma |- of_app (lam (T1 n1) (R n1)) n1 (T n1) (D4 n1) (D5 n1) n :
     of (app (lam (T1 n1) (R n1)) n1) (T n1)}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2.2>> search.
  
  Subgoal subject_reduction_wsscbv.2.3:
  
  Vars: D4:(o) -> (o) -> o, D5:(o) -> (o) -> o, D6:(o) -> (o) -> o, D3:
          (o) -> (o) -> o, M3:(o) -> (o) -> o, T1:(o) -> (o) -> o, R:
          (o) -> (o) -> (o) -> o, T:(o) -> (o) -> o
  Nominals: n2:o, n1:o, n:o
  Contexts: Gamma{}:c[(n1:tm, n2:of n1 (D4 n1 n2))]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n1 n2 n : tm}*
  H4:{T1 n1 n2 : ty}*
  H5:{M3 n1 n2 : tm}*
  H6:{n1 : tm}*
  H7:{D3 n1 n2 : sscbv (M3 n1 n2) n1}*
  H8:{Gamma |- lam (T1 n1 n2) (R n1 n2) : tm}
  H9:{Gamma |- M3 n1 n2 : tm}
  H10:{Gamma |- T n1 n2 : ty}
  H11:{Gamma |- D4 n1 n2 : ty}
  H12:
      {Gamma |- D5 n1 n2 :
        of (lam (T1 n1 n2) (R n1 n2)) (arr (D4 n1 n2) (T n1 n2))}
  H13:{Gamma |- D6 n1 n2 : of (M3 n1 n2) (D4 n1 n2)}
  H15:{Gamma |- n1 : tm}
  
  ==================================
  {Gamma |- 
    of_app (lam (T1 n1 n2) (R n1 n2)) n1 (T n1 n2) (D4 n1 n2) (D5 n1 n2) n2 :
    of (app (lam (T1 n1 n2) (R n1 n2)) n1) (T n1 n2)}
  
  Subgoal subject_reduction_wsscbv.2.4 is:
   {Gamma |- of_app (lam (T1 n1) (R n1)) n1 (T n1) (D4 n1) (D5 n1) n :
     of (app (lam (T1 n1) (R n1)) n1) (T n1)}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2.3>> search.
  
  Subgoal subject_reduction_wsscbv.2.4:
  
  Vars: D4:(o) -> o, D5:(o) -> o, D6:(o) -> o, D3:(o) -> o, M3:(o) -> o, T1:
          (o) -> o, R:(o) -> (o) -> o, T:(o) -> o
  Nominals: n1:o, n:o
  Contexts: Gamma{}:c[(n1:tm, n:of n1 (D4 n1))]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{n:tm |- R n1 n : tm}*
  H4:{T1 n1 : ty}*
  H5:{M3 n1 : tm}*
  H6:{n1 : tm}*
  H7:{D3 n1 : sscbv (M3 n1) n1}*
  H8:{Gamma |- lam (T1 n1) (R n1) : tm}
  H9:{Gamma |- M3 n1 : tm}
  H10:{Gamma |- T n1 : ty}
  H11:{Gamma |- D4 n1 : ty}
  H12:{Gamma |- D5 n1 : of (lam (T1 n1) (R n1)) (arr (D4 n1) (T n1))}
  H13:{Gamma |- D6 n1 : of (M3 n1) (D4 n1)}
  H15:{Gamma |- n1 : tm}
  
  ==================================
  {Gamma |- of_app (lam (T1 n1) (R n1)) n1 (T n1) (D4 n1) (D5 n1) n :
    of (app (lam (T1 n1) (R n1)) n1) (T n1)}
  
  Subgoal subject_reduction_wsscbv.3 is:
   exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.2.4>> search.
  
  Subgoal subject_reduction_wsscbv.3:
  
  Vars: D3:o, M3:o, M4:o, N:o, D1:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of (app M3 N) T}
  H3:{M3 : tm}*
  H4:{M4 : tm}*
  H5:{N : tm}*
  H6:{D3 : sscbv M3 M4}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.3>> search.
  Cannot apply search to goal formula of this structure.
  
  Subgoal subject_reduction_wsscbv.3:
  
  Vars: D3:o, M3:o, M4:o, N:o, D1:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of (app M3 N) T}
  H3:{M3 : tm}*
  H4:{M4 : tm}*
  H5:{N : tm}*
  H6:{D3 : sscbv M3 M4}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.3>> cases H1.
  
  Subgoal subject_reduction_wsscbv.3:
  
  Vars: U:o, a1:o, a2:o, D3:o, M3:o, M4:o, N:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M3 : tm}*
  H4:{M4 : tm}*
  H5:{N : tm}*
  H6:{D3 : sscbv M3 M4}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.3>> apply IH to H11 H6.
  
  Subgoal subject_reduction_wsscbv.3:
  
  Vars: U:o, a1:o, a2:o, D3:o, M3:o, M4:o, N:o, D1:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M3 : tm}*
  H4:{M4 : tm}*
  H5:{N : tm}*
  H6:{D3 : sscbv M3 M4}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  H13:{Gamma |- D1 : of M4 (arr U T)}
  
  ==================================
  exists D3, {Gamma |- D3 : of (app M4 N) T}
  
  subject_reduction_wsscbv.3>> exists of_app M4 N T U D1 a2.
  
  Subgoal subject_reduction_wsscbv.3:
  
  Vars: U:o, a1:o, a2:o, D3:o, M3:o, M4:o, N:o, D1:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M3 : tm}*
  H4:{M4 : tm}*
  H5:{N : tm}*
  H6:{D3 : sscbv M3 M4}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  H13:{Gamma |- D1 : of M4 (arr U T)}
  
  ==================================
  {Gamma |- of_app M4 N T U D1 a2 : of (app M4 N) T}
  
  subject_reduction_wsscbv.3>> assert {Gamma |- M4 : tm}.
  
  Subgoal subject_reduction_wsscbv.3:
  
  Vars: U:o, a1:o, a2:o, D3:o, M3:o, M4:o, N:o, D1:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M3 : tm}*
  H4:{M4 : tm}*
  H5:{N : tm}*
  H6:{D3 : sscbv M3 M4}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  H13:{Gamma |- D1 : of M4 (arr U T)}
  H14:{Gamma |- M4 : tm}
  
  ==================================
  {Gamma |- of_app M4 N T U D1 a2 : of (app M4 N) T}
  
  subject_reduction_wsscbv.3>> cases H13.
  
  Subgoal subject_reduction_wsscbv.3.1:
  
  Vars: a3:(o) -> (o) -> o, R:(o) -> o, U:o, a1:o, a2:o, D3:o, M3:o, N:o, T:o
  Nominals: n2:o, n1:o, n:o
  Contexts: Gamma{n2, n1, n}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M3 : tm}*
  H4:{lam U R : tm}*
  H5:{N : tm}*
  H6:{D3 : sscbv M3 (lam U R)}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  H14:{Gamma |- lam U R : tm}
  H15:{Gamma, n:tm |- R n : tm}
  H16:{Gamma |- U : ty}
  H17:{Gamma |- T : ty}
  H18:{Gamma, n1:tm, n2:of n1 U |- a3 n1 n2 : of (R n1) T}
  
  ==================================
  {Gamma |- of_app (lam U R) N T U (of_lam R U T a3) a2 :
    of (app (lam U R) N) T}
  
  Subgoal subject_reduction_wsscbv.3.2 is:
   {Gamma |- of_app (app M N1) N T U (of_app M N1 (arr U T) U1 a3 a4) a2 :
     of (app (app M N1) N) T}
  
  Subgoal subject_reduction_wsscbv.3.3 is:
   {Gamma |- of_app n (N n n1) (T n n1) (U n n1) n1 (a2 n n1) :
     of (app n (N n n1)) (T n n1)}
  
  subject_reduction_wsscbv.3.1>> search.
  
  Subgoal subject_reduction_wsscbv.3.2:
  
  Vars: U1:o, a3:o, a4:o, M:o, N1:o, U:o, a1:o, a2:o, D3:o, M3:o, N:o, T:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M3 : tm}*
  H4:{app M N1 : tm}*
  H5:{N : tm}*
  H6:{D3 : sscbv M3 (app M N1)}*
  H7:{Gamma |- M3 : tm}
  H8:{Gamma |- N : tm}
  H9:{Gamma |- T : ty}
  H10:{Gamma |- U : ty}
  H11:{Gamma |- a1 : of M3 (arr U T)}
  H12:{Gamma |- a2 : of N U}
  H14:{Gamma |- app M N1 : tm}
  H15:{Gamma |- M : tm}
  H16:{Gamma |- N1 : tm}
  H17:{Gamma |- arr U T : ty}
  H18:{Gamma |- U1 : ty}
  H19:{Gamma |- a3 : of M (arr U1 (arr U T))}
  H20:{Gamma |- a4 : of N1 U1}
  
  ==================================
  {Gamma |- of_app (app M N1) N T U (of_app M N1 (arr U T) U1 a3 a4) a2 :
    of (app (app M N1) N) T}
  
  Subgoal subject_reduction_wsscbv.3.3 is:
   {Gamma |- of_app n (N n n1) (T n n1) (U n n1) n1 (a2 n n1) :
     of (app n (N n n1)) (T n n1)}
  
  subject_reduction_wsscbv.3.2>> search.
  
  Subgoal subject_reduction_wsscbv.3.3:
  
  Vars: U:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, D3:
          (o) -> (o) -> o, M3:(o) -> (o) -> o, N:(o) -> (o) -> o, T:
          (o) -> (o) -> o
  Nominals: n1:o, n:o
  Contexts: Gamma{}:c[(n:tm, n1:of n (arr (U n n1) (T n n1)))]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : sscbv M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M3 n n1 : tm}*
  H4:{n : tm}*
  H5:{N n n1 : tm}*
  H6:{D3 n n1 : sscbv (M3 n n1) n}*
  H7:{Gamma |- M3 n n1 : tm}
  H8:{Gamma |- N n n1 : tm}
  H9:{Gamma |- T n n1 : ty}
  H10:{Gamma |- U n n1 : ty}
  H11:{Gamma |- a1 n n1 : of (M3 n n1) (arr (U n n1) (T n n1))}
  H12:{Gamma |- a2 n n1 : of (N n n1) (U n n1)}
  H14:{Gamma |- n : tm}
  
  ==================================
  {Gamma |- of_app n (N n n1) (T n n1) (U n n1) n1 (a2 n n1) :
    of (app n (N n n1)) (T n n1)}
  
  subject_reduction_wsscbv.3.3>> search.
  Proof Completed!
  
  >> Syntax error: file small_step.ath, line 47, character 8.
  [1]

  $ adelfa -i large_step.ath
  Welcome!
  >> Specification reduce.lf.
  
  >> Schema c := {T}(x:tm,y:of x T).
  
  >> Theorem subject_reduction_lscbn:
      ctx  Gamma:c,
        forall  M1 M2 T D1 D2,
          {Gamma |- D1 : of M1 T} =>
            {D2 : lscbn M1 M2} => exists  D3, {Gamma |- D3 : of M2 T}.
  
  Subgoal subject_reduction_lscbn:
  
  
  ==================================
  ctx Gamma:c.
    forall M1, forall M2, forall T, forall D1, forall D2,
      {Gamma |- D1 : of M1 T} =>
          {D2 : lscbn M1 M2} => exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction_lscbn>> induction on 2.
  
  Subgoal subject_reduction_lscbn:
  
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  
  ==================================
  ctx Gamma:c.
    forall M1, forall M2, forall T, forall D1, forall D2,
      {Gamma |- D1 : of M1 T} =>
          {D2 : lscbn M1 M2}@ => exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction_lscbn>> intros.
  
  Subgoal subject_reduction_lscbn:
  
  Vars: D2:o, D1:o, T:o, M2:o, M1:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of M1 T}
  H2:{D2 : lscbn M1 M2}@
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  subject_reduction_lscbn>> cases H2.
  
  Subgoal subject_reduction_lscbn.1:
  
  Vars: R:(o) -> o, T1:o, D3:o, D4:o, M:o, N:o, D1:o, T:o, M2:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of (app M N) T}
  H3:{M : tm}*
  H4:{N : tm}*
  H5:{M2 : tm}*
  H6:{n:tm |- R n : tm}*
  H7:{T1 : ty}*
  H8:{D3 : lscbn M (lam T1 R)}*
  H9:{D4 : lscbn (R N) M2}*
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  Subgoal subject_reduction_lscbn.2 is:
   exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.1>> cases H1.
  
  Subgoal subject_reduction_lscbn.1:
  
  Vars: D5:o, D6:o, D7:o, R:(o) -> o, T1:o, D3:o, D4:o, M:o, N:o, T:o, M2:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M : tm}*
  H4:{N : tm}*
  H5:{M2 : tm}*
  H6:{n:tm |- R n : tm}*
  H7:{T1 : ty}*
  H8:{D3 : lscbn M (lam T1 R)}*
  H9:{D4 : lscbn (R N) M2}*
  H10:{Gamma |- M : tm}
  H11:{Gamma |- N : tm}
  H12:{Gamma |- T : ty}
  H13:{Gamma |- D5 : ty}
  H14:{Gamma |- D6 : of M (arr D5 T)}
  H15:{Gamma |- D7 : of N D5}
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  Subgoal subject_reduction_lscbn.2 is:
   exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.1>> apply IH to H14 H8.
  
  Subgoal subject_reduction_lscbn.1:
  
  Vars: D5:o, D6:o, D7:o, R:(o) -> o, T1:o, D3:o, D4:o, M:o, N:o, D1:(o) -> o,
          T:o, M2:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M : tm}*
  H4:{N : tm}*
  H5:{M2 : tm}*
  H6:{n:tm |- R n : tm}*
  H7:{T1 : ty}*
  H8:{D3 : lscbn M (lam T1 R)}*
  H9:{D4 : lscbn (R N) M2}*
  H10:{Gamma |- M : tm}
  H11:{Gamma |- N : tm}
  H12:{Gamma |- T : ty}
  H13:{Gamma |- D5 : ty}
  H14:{Gamma |- D6 : of M (arr D5 T)}
  H15:{Gamma |- D7 : of N D5}
  H16:{Gamma |- D1 n : of (lam T1 R) (arr D5 T)}
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  Subgoal subject_reduction_lscbn.2 is:
   exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.1>> cases H16.
  
  Subgoal subject_reduction_lscbn.1:
  
  Vars: a1:(o) -> (o) -> (o) -> o, D5:o, D6:o, D7:o, R:(o) -> o, D3:o, D4:o, M:
          o, N:o, T:o, M2:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M : tm}*
  H4:{N : tm}*
  H5:{M2 : tm}*
  H6:{n:tm |- R n : tm}*
  H7:{D5 : ty}*
  H8:{D3 : lscbn M (lam D5 R)}*
  H9:{D4 : lscbn (R N) M2}*
  H10:{Gamma |- M : tm}
  H11:{Gamma |- N : tm}
  H12:{Gamma |- T : ty}
  H13:{Gamma |- D5 : ty}
  H14:{Gamma |- D6 : of M (arr D5 T)}
  H15:{Gamma |- D7 : of N D5}
  H17:{Gamma, n1:tm |- R n1 : tm}
  H18:{Gamma |- D5 : ty}
  H19:{Gamma |- T : ty}
  H20:{Gamma, n2:tm, n3:of n2 D5 |- a1 n n2 n3 : of (R n2) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  Subgoal subject_reduction_lscbn.2 is:
   exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.1>> inst H20 with n2 = N.
  
  Subgoal subject_reduction_lscbn.1:
  
  Vars: a1:(o) -> (o) -> (o) -> o, D5:o, D6:o, D7:o, R:(o) -> o, D3:o, D4:o, M:
          o, N:o, T:o, M2:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M : tm}*
  H4:{N : tm}*
  H5:{M2 : tm}*
  H6:{n:tm |- R n : tm}*
  H7:{D5 : ty}*
  H8:{D3 : lscbn M (lam D5 R)}*
  H9:{D4 : lscbn (R N) M2}*
  H10:{Gamma |- M : tm}
  H11:{Gamma |- N : tm}
  H12:{Gamma |- T : ty}
  H13:{Gamma |- D5 : ty}
  H14:{Gamma |- D6 : of M (arr D5 T)}
  H15:{Gamma |- D7 : of N D5}
  H17:{Gamma, n1:tm |- R n1 : tm}
  H18:{Gamma |- D5 : ty}
  H19:{Gamma |- T : ty}
  H20:{Gamma, n2:tm, n3:of n2 D5 |- a1 n n2 n3 : of (R n2) T}
  H21:{Gamma, n3:of N D5 |- a1 n N n3 : of (R N) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  Subgoal subject_reduction_lscbn.2 is:
   exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.1>> inst H21 with n3 = D7.
  
  Subgoal subject_reduction_lscbn.1:
  
  Vars: a1:(o) -> (o) -> (o) -> o, D5:o, D6:o, D7:o, R:(o) -> o, D3:o, D4:o, M:
          o, N:o, T:o, M2:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M : tm}*
  H4:{N : tm}*
  H5:{M2 : tm}*
  H6:{n:tm |- R n : tm}*
  H7:{D5 : ty}*
  H8:{D3 : lscbn M (lam D5 R)}*
  H9:{D4 : lscbn (R N) M2}*
  H10:{Gamma |- M : tm}
  H11:{Gamma |- N : tm}
  H12:{Gamma |- T : ty}
  H13:{Gamma |- D5 : ty}
  H14:{Gamma |- D6 : of M (arr D5 T)}
  H15:{Gamma |- D7 : of N D5}
  H17:{Gamma, n1:tm |- R n1 : tm}
  H18:{Gamma |- D5 : ty}
  H19:{Gamma |- T : ty}
  H20:{Gamma, n2:tm, n3:of n2 D5 |- a1 n n2 n3 : of (R n2) T}
  H21:{Gamma, n3:of N D5 |- a1 n N n3 : of (R N) T}
  H22:{Gamma |- a1 n N D7 : of (R N) T}
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  Subgoal subject_reduction_lscbn.2 is:
   exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.1>> apply IH to H22 H9.
  
  Subgoal subject_reduction_lscbn.1:
  
  Vars: a1:(o) -> (o) -> (o) -> o, D5:o, D6:o, D7:o, R:(o) -> o, D3:o, D4:o, M:
          o, N:o, D1:(o) -> (o) -> (o) -> (o) -> o, T:o, M2:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M : tm}*
  H4:{N : tm}*
  H5:{M2 : tm}*
  H6:{n:tm |- R n : tm}*
  H7:{D5 : ty}*
  H8:{D3 : lscbn M (lam D5 R)}*
  H9:{D4 : lscbn (R N) M2}*
  H10:{Gamma |- M : tm}
  H11:{Gamma |- N : tm}
  H12:{Gamma |- T : ty}
  H13:{Gamma |- D5 : ty}
  H14:{Gamma |- D6 : of M (arr D5 T)}
  H15:{Gamma |- D7 : of N D5}
  H17:{Gamma, n1:tm |- R n1 : tm}
  H18:{Gamma |- D5 : ty}
  H19:{Gamma |- T : ty}
  H20:{Gamma, n2:tm, n3:of n2 D5 |- a1 n n2 n3 : of (R n2) T}
  H21:{Gamma, n3:of N D5 |- a1 n N n3 : of (R N) T}
  H22:{Gamma |- a1 n N D7 : of (R N) T}
  H23:{Gamma |- D1 n3 n2 n1 n : of M2 T}
  
  ==================================
  exists D3, {Gamma |- D3 : of M2 T}
  
  Subgoal subject_reduction_lscbn.2 is:
   exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.1>> exists D1 n3 n2 n1 n.
  
  Subgoal subject_reduction_lscbn.1:
  
  Vars: a1:(o) -> (o) -> (o) -> o, D5:o, D6:o, D7:o, R:(o) -> o, D3:o, D4:o, M:
          o, N:o, D1:(o) -> (o) -> (o) -> (o) -> o, T:o, M2:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: Gamma{n3, n2, n1}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H3:{M : tm}*
  H4:{N : tm}*
  H5:{M2 : tm}*
  H6:{n:tm |- R n : tm}*
  H7:{D5 : ty}*
  H8:{D3 : lscbn M (lam D5 R)}*
  H9:{D4 : lscbn (R N) M2}*
  H10:{Gamma |- M : tm}
  H11:{Gamma |- N : tm}
  H12:{Gamma |- T : ty}
  H13:{Gamma |- D5 : ty}
  H14:{Gamma |- D6 : of M (arr D5 T)}
  H15:{Gamma |- D7 : of N D5}
  H17:{Gamma, n1:tm |- R n1 : tm}
  H18:{Gamma |- D5 : ty}
  H19:{Gamma |- T : ty}
  H20:{Gamma, n2:tm, n3:of n2 D5 |- a1 n n2 n3 : of (R n2) T}
  H21:{Gamma, n3:of N D5 |- a1 n N n3 : of (R N) T}
  H22:{Gamma |- a1 n N D7 : of (R N) T}
  H23:{Gamma |- D1 n3 n2 n1 n : of M2 T}
  
  ==================================
  {Gamma |- D1 n3 n2 n1 n : of M2 T}
  
  Subgoal subject_reduction_lscbn.2 is:
   exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.1>> search.
  
  Subgoal subject_reduction_lscbn.2:
  
  Vars: T1:o, R:(o) -> o, D1:o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of (lam T1 R) T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  
  ==================================
  exists D3, {Gamma |- D3 : of (lam T1 R) T}
  
  subject_reduction_lscbn.2>> exists D1.
  
  Subgoal subject_reduction_lscbn.2:
  
  Vars: T1:o, R:(o) -> o, D1:o, T:o
  Nominals: n:o
  Contexts: Gamma{}:c[]
  IH:
      ctx Gamma:c.
        forall M1, forall M2, forall T, forall D1, forall D2,
          {Gamma |- D1 : of M1 T} =>
              {D2 : lscbn M1 M2}* => exists D3, {Gamma |- D3 : of M2 T}
  H1:{Gamma |- D1 : of (lam T1 R) T}
  H3:{n:tm |- R n : tm}*
  H4:{T1 : ty}*
  
  ==================================
  {Gamma |- D1 : of (lam T1 R) T}
  
  subject_reduction_lscbn.2>> search.
  Proof Completed!
  
  >> Goodbye!
