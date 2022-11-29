  $ adelfa -i cut.ath
  Welcome!
  >> Specification cut.lf.
  
  >> Schema c := {A}(x:hyp A).
  
  >> Theorem imp_inv:
      ctx  G:c,
        forall  A B D,
          {G |- D : conc imp A B} =>
            exists  D':(o) -> o, {G |- [x]D' x : {x:hyp A}conc B}.
  
  Subgoal imp_inv:
  
  
  ==================================
  ctx G:c.
    forall A, forall B, forall D,
      {G |- D : conc (imp A B)} => exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv>> induction on 1.
  
  Subgoal imp_inv:
  
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  ==================================
  ctx G:c.
    forall A, forall B, forall D,
      {G |- D : conc (imp A B)}@ => exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv>> intros.
  
  Subgoal imp_inv:
  
  Vars: D:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- D : conc (imp A B)}@
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv>> cases H1.
  
  Subgoal imp_inv.1:
  
  Vars: D1:(o) -> o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impR A B ([c7]D1 c7) : conc (imp A B)}@
  H2:{G |- A : proptm}*
  H3:{G |- B : proptm}*
  H4:{G, n:hyp A |- D1 n : conc B}*
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.2 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.1>> exists D1.
  
  Subgoal imp_inv.1:
  
  Vars: D1:(o) -> o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impR A B ([c7]D1 c7) : conc (imp A B)}@
  H2:{G |- A : proptm}*
  H3:{G |- B : proptm}*
  H4:{G, n:hyp A |- D1 n : conc B}*
  
  ==================================
  {G |- [x]D1 x : {x:hyp A}conc B}
  
  Subgoal imp_inv.2 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.1>> search.
  
  Subgoal imp_inv.2:
  
  Vars: A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> apply IH to H6 with (G = G,n:hyp B1), A = A, B = B, D = D2 n.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> exists [x]impL A1 B1 B D1 ([y]D' y x) D3.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  
  ==================================
  {G |- [x]impL A1 B1 B D1 ([y]D' y x) D3 : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> cases H4.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  
  ==================================
  {G |- [x]impL A1 B1 B D1 ([c57]D' c57 x) D3 : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> weaken H2 with hyp A.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n2:hyp A |- A1 : proptm}*
  
  ==================================
  {G |- [x]impL A1 B1 B D1 ([c57]D' c57 x) D3 : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> weaken H3 with hyp A.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n2:hyp A |- A1 : proptm}*
  H12:{G, n3:hyp A |- B1 : proptm}*
  
  ==================================
  {G |- [x]impL A1 B1 B D1 ([c57]D' c57 x) D3 : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> weaken H10 with hyp A.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n2:hyp A |- A1 : proptm}*
  H12:{G, n3:hyp A |- B1 : proptm}*
  H13:{G, n4:hyp A |- B : proptm}*
  
  ==================================
  {G |- [x]impL A1 B1 B D1 ([c57]D' c57 x) D3 : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> weaken H5 with hyp A.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n2:hyp A |- A1 : proptm}*
  H12:{G, n3:hyp A |- B1 : proptm}*
  H13:{G, n4:hyp A |- B : proptm}*
  H14:{G, n5:hyp A |- D1 : conc A1}*
  
  ==================================
  {G |- [x]impL A1 B1 B D1 ([c57]D' c57 x) D3 : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> ctxpermute H8 to G,n1:hyp A,n:hyp B1.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n2:hyp A |- A1 : proptm}*
  H12:{G, n3:hyp A |- B1 : proptm}*
  H13:{G, n4:hyp A |- B : proptm}*
  H14:{G, n5:hyp A |- D1 : conc A1}*
  H15:{G, n1:hyp A, n:hyp B1 |- D' n n1 : conc B}
  
  ==================================
  {G |- [x]impL A1 B1 B D1 ([c57]D' c57 x) D3 : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> weaken H7 with hyp A.
  
  Subgoal imp_inv.2:
  
  Vars: D':(o) -> (o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- impL A1 B1 (imp A B) D1 ([c15]D2 c15) D3 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (imp A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1, n1:hyp A |- D' n n1 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n2:hyp A |- A1 : proptm}*
  H12:{G, n3:hyp A |- B1 : proptm}*
  H13:{G, n4:hyp A |- B : proptm}*
  H14:{G, n5:hyp A |- D1 : conc A1}*
  H15:{G, n1:hyp A, n:hyp B1 |- D' n n1 : conc B}
  H16:{G, n6:hyp A |- D3 : hyp (imp A1 B1)}*
  
  ==================================
  {G |- [x]impL A1 B1 B D1 ([c57]D' c57 x) D3 : {x:hyp A}conc B}
  
  Subgoal imp_inv.3 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.2>> search.
  
  Subgoal imp_inv.3:
  
  Vars: A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> apply IH to H5 with (G = G,n:hyp A1,n1:hyp B1).
  
  Subgoal imp_inv.3:
  
  Vars: D':(o) -> (o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A
          :o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:{G, n:hyp A1, n1:hyp B1, n2:hyp A |- D' n1 n n2 : conc B}
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> ctxpermute H7 to G,n2:hyp A,n:hyp A1,n1:hyp B1.
  
  Subgoal imp_inv.3:
  
  Vars: D':(o) -> (o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A
          :o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:{G, n:hyp A1, n1:hyp B1, n2:hyp A |- D' n1 n n2 : conc B}
  H8:{G, n2:hyp A, n:hyp A1, n1:hyp B1 |- D' n1 n n2 : conc B}
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> exists [x]andL A1 B1 B ([y][z]D' z y x) D2.
  
  Subgoal imp_inv.3:
  
  Vars: D':(o) -> (o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A
          :o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:{G, n:hyp A1, n1:hyp B1, n2:hyp A |- D' n1 n n2 : conc B}
  H8:{G, n2:hyp A, n:hyp A1, n1:hyp B1 |- D' n1 n n2 : conc B}
  
  ==================================
  {G |- [x]andL A1 B1 B ([y][z]D' z y x) D2 : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> cases H4.
  
  Subgoal imp_inv.3:
  
  Vars: D':(o) -> (o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A
          :o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:{G, n:hyp A1, n1:hyp B1, n2:hyp A |- D' n1 n n2 : conc B}
  H8:{G, n2:hyp A, n:hyp A1, n1:hyp B1 |- D' n1 n n2 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  
  ==================================
  {G |- [x]andL A1 B1 B ([c82][c83]D' c83 c82 x) D2 : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> weaken H2 with hyp A.
  
  Subgoal imp_inv.3:
  
  Vars: D':(o) -> (o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A
          :o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:{G, n:hyp A1, n1:hyp B1, n2:hyp A |- D' n1 n n2 : conc B}
  H8:{G, n2:hyp A, n:hyp A1, n1:hyp B1 |- D' n1 n n2 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n3:hyp A |- A1 : proptm}*
  
  ==================================
  {G |- [x]andL A1 B1 B ([c82][c83]D' c83 c82 x) D2 : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> weaken H3 with hyp A.
  
  Subgoal imp_inv.3:
  
  Vars: D':(o) -> (o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A
          :o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:{G, n:hyp A1, n1:hyp B1, n2:hyp A |- D' n1 n n2 : conc B}
  H8:{G, n2:hyp A, n:hyp A1, n1:hyp B1 |- D' n1 n n2 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n3:hyp A |- A1 : proptm}*
  H12:{G, n4:hyp A |- B1 : proptm}*
  
  ==================================
  {G |- [x]andL A1 B1 B ([c82][c83]D' c83 c82 x) D2 : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> weaken H6 with hyp A.
  
  Subgoal imp_inv.3:
  
  Vars: D':(o) -> (o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A
          :o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:{G, n:hyp A1, n1:hyp B1, n2:hyp A |- D' n1 n n2 : conc B}
  H8:{G, n2:hyp A, n:hyp A1, n1:hyp B1 |- D' n1 n n2 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n3:hyp A |- A1 : proptm}*
  H12:{G, n4:hyp A |- B1 : proptm}*
  H13:{G, n5:hyp A |- D2 : hyp (and A1 B1)}*
  
  ==================================
  {G |- [x]andL A1 B1 B ([c82][c83]D' c83 c82 x) D2 : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> weaken H10 with hyp A.
  
  Subgoal imp_inv.3:
  
  Vars: D':(o) -> (o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A
          :o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5, n6}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- andL A1 B1 (imp A B) ([c29][c30]D1 c29 c30) D2 : conc (imp A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- imp A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (imp A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:{G, n:hyp A1, n1:hyp B1, n2:hyp A |- D' n1 n n2 : conc B}
  H8:{G, n2:hyp A, n:hyp A1, n1:hyp B1 |- D' n1 n n2 : conc B}
  H9:{G |- A : proptm}*
  H10:{G |- B : proptm}*
  H11:{G, n3:hyp A |- A1 : proptm}*
  H12:{G, n4:hyp A |- B1 : proptm}*
  H13:{G, n5:hyp A |- D2 : hyp (and A1 B1)}*
  H14:{G, n6:hyp A |- B : proptm}*
  
  ==================================
  {G |- [x]andL A1 B1 B ([c82][c83]D' c83 c82 x) D2 : {x:hyp A}conc B}
  
  Subgoal imp_inv.4 is:
   exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.3>> search.
  
  Subgoal imp_inv.4:
  
  Vars: D1:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- init (imp A B) D1 : conc (imp A B)}@
  H2:{G |- imp A B : proptm}*
  H3:{G |- D1 : hyp (imp A B)}*
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp A}conc B}
  
  imp_inv.4>> cases H3.
  
  Subgoal imp_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (imp (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- init (imp (A n) (B n)) n : conc (imp (A n) (B n))}@
  H2:{G |- imp (A n) (B n) : proptm}*
  
  ==================================
  exists D', {G |- [x]D' x : {x:hyp (A n)}conc (B n)}
  
  imp_inv.4>> exists [x]impL A n B n B n init A n x ([y]init B n y) n.
  
  Subgoal imp_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (imp (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- init (imp (A n) (B n)) n : conc (imp (A n) (B n))}@
  H2:{G |- imp (A n) (B n) : proptm}*
  
  ==================================
  {G |- [x]impL (A n) (B n) (B n) (init (A n) x) ([y]init (B n) y) n :
    {x:hyp (A n)}conc (B n)}
  
  imp_inv.4>> cases H2.
  
  Subgoal imp_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (imp (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- init (imp (A n) (B n)) n : conc (imp (A n) (B n))}@
  H2:{G |- imp (A n) (B n) : proptm}*
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  
  ==================================
  {G |- [x]impL (A n) (B n) (B n) (init (A n) x) ([c110]init (B n) c110) n :
    {x:hyp (A n)}conc (B n)}
  
  imp_inv.4>> weaken H4 with hyp A n.
  
  Subgoal imp_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n1}:c[(n:hyp (imp (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- init (imp (A n) (B n)) n : conc (imp (A n) (B n))}@
  H2:{G |- imp (A n) (B n) : proptm}*
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  H6:{G, n1:hyp (A n) |- A n : proptm}*
  
  ==================================
  {G |- [x]impL (A n) (B n) (B n) (init (A n) x) ([c110]init (B n) c110) n :
    {x:hyp (A n)}conc (B n)}
  
  imp_inv.4>> weaken H5 with hyp A n.
  
  Subgoal imp_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n1, n2}:c[(n:hyp (imp (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- init (imp (A n) (B n)) n : conc (imp (A n) (B n))}@
  H2:{G |- imp (A n) (B n) : proptm}*
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  H6:{G, n1:hyp (A n) |- A n : proptm}*
  H7:{G, n2:hyp (A n) |- B n : proptm}*
  
  ==================================
  {G |- [x]impL (A n) (B n) (B n) (init (A n) x) ([c110]init (B n) c110) n :
    {x:hyp (A n)}conc (B n)}
  
  imp_inv.4>> weaken H7 with hyp B n.
  
  Subgoal imp_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n1, n2, n3}:c[(n:hyp (imp (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (imp A B)}* =>
              exists D', {G |- [x]D' x : {x:hyp A}conc B}
  H1:{G |- init (imp (A n) (B n)) n : conc (imp (A n) (B n))}@
  H2:{G |- imp (A n) (B n) : proptm}*
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  H6:{G, n1:hyp (A n) |- A n : proptm}*
  H7:{G, n2:hyp (A n) |- B n : proptm}*
  H8:{G, n2:hyp (A n), n3:hyp (B n) |- B n : proptm}*
  
  ==================================
  {G |- [x]impL (A n) (B n) (B n) (init (A n) x) ([c110]init (B n) c110) n :
    {x:hyp (A n)}conc (B n)}
  
  imp_inv.4>> search.
  Proof Completed!
  
  >> Theorem and_inv:
      ctx  G:c,
        forall  A B D,
          {G |- D : conc and A B} =>
            exists  D1 D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}.
  
  Subgoal and_inv:
  
  
  ==================================
  ctx G:c.
    forall A, forall B, forall D,
      {G |- D : conc (and A B)} =>
          exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv>> induction on 1.
  
  Subgoal and_inv:
  
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  ==================================
  ctx G:c.
    forall A, forall B, forall D,
      {G |- D : conc (and A B)}@ =>
          exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv>> intros.
  
  Subgoal and_inv:
  
  Vars: D:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- D : conc (and A B)}@
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv>> cases H1.
  
  Subgoal and_inv.1:
  
  Vars: A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> apply IH to H6 with (G = G,n:hyp B1), A = A, B = B, D = D2 n.
  
  Subgoal and_inv.1:
  
  Vars: D5:(o) -> o, D4:(o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H8:{G, n:hyp B1 |- D4 n : conc A} /\ {G, n:hyp B1 |- D5 n : conc B}
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> cases H8.
  
  Subgoal and_inv.1:
  
  Vars: D5:(o) -> o, D4:(o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H9:{G, n:hyp B1 |- D4 n : conc A}
  H10:{G, n:hyp B1 |- D5 n : conc B}
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> exists impL A1 B1 A D1 ([y]D4 y) D3.
  
  Subgoal and_inv.1:
  
  Vars: D5:(o) -> o, D4:(o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H9:{G, n:hyp B1 |- D4 n : conc A}
  H10:{G, n:hyp B1 |- D5 n : conc B}
  
  ==================================
  exists D2, {G |- impL A1 B1 A D1 ([y]D4 y) D3 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> exists impL A1 B1 B D1 ([y]D5 y) D3.
  
  Subgoal and_inv.1:
  
  Vars: D5:(o) -> o, D4:(o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H9:{G, n:hyp B1 |- D4 n : conc A}
  H10:{G, n:hyp B1 |- D5 n : conc B}
  
  ==================================
  {G |- impL A1 B1 A D1 ([y]D4 y) D3 : conc A} /\
      {G |- impL A1 B1 B D1 ([y]D5 y) D3 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> split.
  
  Subgoal and_inv.1:
  
  Vars: D5:(o) -> o, D4:(o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H9:{G, n:hyp B1 |- D4 n : conc A}
  H10:{G, n:hyp B1 |- D5 n : conc B}
  
  ==================================
  {G |- impL A1 B1 A D1 ([y]D4 y) D3 : conc A}
  
  Subgoal and_inv.1 is:
   {G |- impL A1 B1 B D1 ([y]D5 y) D3 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> cases H4.
  
  Subgoal and_inv.1:
  
  Vars: D5:(o) -> o, D4:(o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H9:{G, n:hyp B1 |- D4 n : conc A}
  H10:{G, n:hyp B1 |- D5 n : conc B}
  H11:{G |- A : proptm}*
  H12:{G |- B : proptm}*
  
  ==================================
  {G |- impL A1 B1 A D1 ([c56]D4 c56) D3 : conc A}
  
  Subgoal and_inv.1 is:
   {G |- impL A1 B1 B D1 ([y]D5 y) D3 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> search.
  
  Subgoal and_inv.1:
  
  Vars: D5:(o) -> o, D4:(o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H9:{G, n:hyp B1 |- D4 n : conc A}
  H10:{G, n:hyp B1 |- D5 n : conc B}
  
  ==================================
  {G |- impL A1 B1 B D1 ([y]D5 y) D3 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> cases H4.
  
  Subgoal and_inv.1:
  
  Vars: D5:(o) -> o, D4:(o) -> o, A1:o, B1:o, D1:o, D2:(o) -> o, D3:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- impL A1 B1 (and A B) D1 ([c15]D2 c15) D3 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G |- D1 : conc A1}*
  H6:{G, n:hyp B1 |- D2 n : conc (and A B)}*
  H7:{G |- D3 : hyp (imp A1 B1)}*
  H9:{G, n:hyp B1 |- D4 n : conc A}
  H10:{G, n:hyp B1 |- D5 n : conc B}
  H11:{G |- A : proptm}*
  H12:{G |- B : proptm}*
  
  ==================================
  {G |- impL A1 B1 B D1 ([c69]D5 c69) D3 : conc B}
  
  Subgoal and_inv.2 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.1>> search.
  
  Subgoal and_inv.2:
  
  Vars: D1:o, D2:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andR A B D1 D2 : conc (and A B)}@
  H2:{G |- A : proptm}*
  H3:{G |- B : proptm}*
  H4:{G |- D1 : conc A}*
  H5:{G |- D2 : conc B}*
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.2>> exists D1.
  
  Subgoal and_inv.2:
  
  Vars: D1:o, D2:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andR A B D1 D2 : conc (and A B)}@
  H2:{G |- A : proptm}*
  H3:{G |- B : proptm}*
  H4:{G |- D1 : conc A}*
  H5:{G |- D2 : conc B}*
  
  ==================================
  exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.2>> exists D2.
  
  Subgoal and_inv.2:
  
  Vars: D1:o, D2:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andR A B D1 D2 : conc (and A B)}@
  H2:{G |- A : proptm}*
  H3:{G |- B : proptm}*
  H4:{G |- D1 : conc A}*
  H5:{G |- D2 : conc B}*
  
  ==================================
  {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.2>> split.
  
  Subgoal and_inv.2:
  
  Vars: D1:o, D2:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andR A B D1 D2 : conc (and A B)}@
  H2:{G |- A : proptm}*
  H3:{G |- B : proptm}*
  H4:{G |- D1 : conc A}*
  H5:{G |- D2 : conc B}*
  
  ==================================
  {G |- D1 : conc A}
  
  Subgoal and_inv.2 is:
   {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.2>> search.
  
  Subgoal and_inv.2:
  
  Vars: D1:o, D2:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andR A B D1 D2 : conc (and A B)}@
  H2:{G |- A : proptm}*
  H3:{G |- B : proptm}*
  H4:{G |- D1 : conc A}*
  H5:{G |- D2 : conc B}*
  
  ==================================
  {G |- D2 : conc B}
  
  Subgoal and_inv.3 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.2>> search.
  
  Subgoal and_inv.3:
  
  Vars: A1:o, B1:o, D1:(o) -> (o) -> o, D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> apply IH to H5 with (G = G,n:hyp A1,n1:hyp B1), A = A, B = B, D = D1 n n1.
  
  Subgoal and_inv.3:
  
  Vars: D4:(o) -> (o) -> o, D3:(o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o,
          D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H7:
      {G, n:hyp A1, n1:hyp B1 |- D3 n1 n : conc A} /\
          {G, n:hyp A1, n1:hyp B1 |- D4 n1 n : conc B}
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> cases H7.
  
  Subgoal and_inv.3:
  
  Vars: D4:(o) -> (o) -> o, D3:(o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o,
          D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H8:{G, n:hyp A1, n1:hyp B1 |- D3 n1 n : conc A}
  H9:{G, n:hyp A1, n1:hyp B1 |- D4 n1 n : conc B}
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> exists andL A1 B1 A ([x][y]D3 y x) D2.
  
  Subgoal and_inv.3:
  
  Vars: D4:(o) -> (o) -> o, D3:(o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o,
          D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H8:{G, n:hyp A1, n1:hyp B1 |- D3 n1 n : conc A}
  H9:{G, n:hyp A1, n1:hyp B1 |- D4 n1 n : conc B}
  
  ==================================
  exists D5,
    {G |- andL A1 B1 A ([x][y]D3 y x) D2 : conc A} /\ {G |- D5 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> exists andL A1 B1 B ([x][y]D4 y x) D2.
  
  Subgoal and_inv.3:
  
  Vars: D4:(o) -> (o) -> o, D3:(o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o,
          D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H8:{G, n:hyp A1, n1:hyp B1 |- D3 n1 n : conc A}
  H9:{G, n:hyp A1, n1:hyp B1 |- D4 n1 n : conc B}
  
  ==================================
  {G |- andL A1 B1 A ([x][y]D3 y x) D2 : conc A} /\
      {G |- andL A1 B1 B ([x][y]D4 y x) D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> split.
  
  Subgoal and_inv.3:
  
  Vars: D4:(o) -> (o) -> o, D3:(o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o,
          D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H8:{G, n:hyp A1, n1:hyp B1 |- D3 n1 n : conc A}
  H9:{G, n:hyp A1, n1:hyp B1 |- D4 n1 n : conc B}
  
  ==================================
  {G |- andL A1 B1 A ([x][y]D3 y x) D2 : conc A}
  
  Subgoal and_inv.3 is:
   {G |- andL A1 B1 B ([x][y]D4 y x) D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> cases H4.
  
  Subgoal and_inv.3:
  
  Vars: D4:(o) -> (o) -> o, D3:(o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o,
          D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H8:{G, n:hyp A1, n1:hyp B1 |- D3 n1 n : conc A}
  H9:{G, n:hyp A1, n1:hyp B1 |- D4 n1 n : conc B}
  H10:{G |- A : proptm}*
  H11:{G |- B : proptm}*
  
  ==================================
  {G |- andL A1 B1 A ([c84][c85]D3 c85 c84) D2 : conc A}
  
  Subgoal and_inv.3 is:
   {G |- andL A1 B1 B ([x][y]D4 y x) D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> search.
  
  Subgoal and_inv.3:
  
  Vars: D4:(o) -> (o) -> o, D3:(o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o,
          D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H8:{G, n:hyp A1, n1:hyp B1 |- D3 n1 n : conc A}
  H9:{G, n:hyp A1, n1:hyp B1 |- D4 n1 n : conc B}
  
  ==================================
  {G |- andL A1 B1 B ([x][y]D4 y x) D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> cases H4.
  
  Subgoal and_inv.3:
  
  Vars: D4:(o) -> (o) -> o, D3:(o) -> (o) -> o, A1:o, B1:o, D1:(o) -> (o) -> o,
          D2:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- andL A1 B1 (and A B) ([c29][c30]D1 c29 c30) D2 : conc (and A B)}@
  H2:{G |- A1 : proptm}*
  H3:{G |- B1 : proptm}*
  H4:{G |- and A B : proptm}*
  H5:{G, n:hyp A1, n1:hyp B1 |- D1 n n1 : conc (and A B)}*
  H6:{G |- D2 : hyp (and A1 B1)}*
  H8:{G, n:hyp A1, n1:hyp B1 |- D3 n1 n : conc A}
  H9:{G, n:hyp A1, n1:hyp B1 |- D4 n1 n : conc B}
  H10:{G |- A : proptm}*
  H11:{G |- B : proptm}*
  
  ==================================
  {G |- andL A1 B1 B ([c98][c99]D4 c99 c98) D2 : conc B}
  
  Subgoal and_inv.4 is:
   exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.3>> search.
  
  Subgoal and_inv.4:
  
  Vars: D1:o, B:o, A:o
  Contexts: G{}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and A B) D1 : conc (and A B)}@
  H2:{G |- and A B : proptm}*
  H3:{G |- D1 : hyp (and A B)}*
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  
  and_inv.4>> cases H3.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H2:{G |- and (A n) (B n) : proptm}*
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc (A n)} /\ {G |- D2 : conc (B n)}
  
  and_inv.4>> cases H2.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  
  ==================================
  exists D1, exists D2, {G |- D1 : conc (A n)} /\ {G |- D2 : conc (B n)}
  
  and_inv.4>> exists andL A n B n A n ([x][y]init A n x) n.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  
  ==================================
  exists D2,
    {G |- andL (A n) (B n) (A n) ([x][y]init (A n) x) n : conc (A n)} /\
        {G |- D2 : conc (B n)}
  
  and_inv.4>> exists andL A n B n B n ([x][y]init B n y) n.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  
  ==================================
  {G |- andL (A n) (B n) (A n) ([x][y]init (A n) x) n : conc (A n)} /\
      {G |- andL (A n) (B n) (B n) ([x][y]init (B n) y) n : conc (B n)}
  
  and_inv.4>> split.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  
  ==================================
  {G |- andL (A n) (B n) (A n) ([x][y]init (A n) x) n : conc (A n)}
  
  Subgoal and_inv.4 is:
   {G |- andL (A n) (B n) (B n) ([x][y]init (B n) y) n : conc (B n)}
  
  and_inv.4>> weaken H4 with hyp A n.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n1}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  H6:{G, n1:hyp (A n) |- A n : proptm}*
  
  ==================================
  {G |- andL (A n) (B n) (A n) ([x][y]init (A n) x) n : conc (A n)}
  
  Subgoal and_inv.4 is:
   {G |- andL (A n) (B n) (B n) ([x][y]init (B n) y) n : conc (B n)}
  
  and_inv.4>> weaken H5 with hyp A n.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n1, n2}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  H6:{G, n1:hyp (A n) |- A n : proptm}*
  H7:{G, n2:hyp (A n) |- B n : proptm}*
  
  ==================================
  {G |- andL (A n) (B n) (A n) ([x][y]init (A n) x) n : conc (A n)}
  
  Subgoal and_inv.4 is:
   {G |- andL (A n) (B n) (B n) ([x][y]init (B n) y) n : conc (B n)}
  
  and_inv.4>> weaken H6 with hyp B n.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n1, n2, n3}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  H6:{G, n1:hyp (A n) |- A n : proptm}*
  H7:{G, n2:hyp (A n) |- B n : proptm}*
  H8:{G, n1:hyp (A n), n3:hyp (B n) |- A n : proptm}*
  
  ==================================
  {G |- andL (A n) (B n) (A n) ([x][y]init (A n) x) n : conc (A n)}
  
  Subgoal and_inv.4 is:
   {G |- andL (A n) (B n) (B n) ([x][y]init (B n) y) n : conc (B n)}
  
  and_inv.4>> search.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n:o
  Contexts: G{}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  
  ==================================
  {G |- andL (A n) (B n) (B n) ([x][y]init (B n) y) n : conc (B n)}
  
  and_inv.4>> weaken H5 with hyp A n.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n1}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  H6:{G, n1:hyp (A n) |- B n : proptm}*
  
  ==================================
  {G |- andL (A n) (B n) (B n) ([x][y]init (B n) y) n : conc (B n)}
  
  and_inv.4>> weaken H6 with hyp B n.
  
  Subgoal and_inv.4:
  
  Vars: B:(o) -> o, A:(o) -> o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n1, n2}:c[(n:hyp (and (A n) (B n)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D,
          {G |- D : conc (and A B)}* =>
              exists D1, exists D2, {G |- D1 : conc A} /\ {G |- D2 : conc B}
  H1:{G |- init (and (A n) (B n)) n : conc (and (A n) (B n))}@
  H4:{G |- A n : proptm}*
  H5:{G |- B n : proptm}*
  H6:{G, n1:hyp (A n) |- B n : proptm}*
  H7:{G, n1:hyp (A n), n2:hyp (B n) |- B n : proptm}*
  
  ==================================
  {G |- andL (A n) (B n) (B n) ([x][y]init (B n) y) n : conc (B n)}
  
  and_inv.4>> search.
  Proof Completed!
  
  >> Theorem cut:
      ctx  G:c,
        forall  A B D1 D2:(o) -> o,
          {A : proptm} =>
            {G |- D1 : conc A} =>
              {G |- [x]D2 x : {x:hyp A}conc B} =>
                exists  D3, {G |- D3 : conc B}.
  
  Subgoal cut:
  
  
  ==================================
  ctx G:c.
    forall A, forall B, forall D1, forall D2,
      {A : proptm} =>
          {G |- D1 : conc A} =>
              {G |- [x]D2 x : {x:hyp A}conc B} => exists D3, {G |- D3 : conc B}
  
  cut>> induction on 1.
  
  Subgoal cut:
  
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  
  ==================================
  ctx G:c.
    forall A, forall B, forall D1, forall D2,
      {A : proptm}@ =>
          {G |- D1 : conc A} =>
              {G |- [x]D2 x : {x:hyp A}conc B} => exists D3, {G |- D3 : conc B}
  
  cut>> induction on 3.
  
  Subgoal cut:
  
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  
  ==================================
  ctx G:c.
    forall A, forall B, forall D1, forall D2,
      {A : proptm}@ =>
          {G |- D1 : conc A} =>
              {G |- [x]D2 x : {x:hyp A}conc B}@@ =>
                  exists D3, {G |- D3 : conc B}
  
  cut>> intros.
  
  Subgoal cut:
  
  Vars: D2:(o) -> o, D1:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- D2 n : conc B}@@
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  cut>> cases H3.
  
  Subgoal cut.1:
  
  Vars: D:(o) -> (o) -> o, B1:o, B2:o, D1:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- impR B1 B2 ([c7]D n c7) : conc (imp B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A, n1:hyp B1 |- D n n1 : conc B2}**
  
  ==================================
  exists D3, {G |- D3 : conc (imp B1 B2)}
  
  Subgoal cut.2 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.1>> ctxpermute H6 to G,n1:hyp B1,n:hyp A.
  
  Subgoal cut.1:
  
  Vars: D:(o) -> (o) -> o, B1:o, B2:o, D1:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- impR B1 B2 ([c7]D n c7) : conc (imp B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A, n1:hyp B1 |- D n n1 : conc B2}**
  H7:{G, n1:hyp B1, n:hyp A |- D n n1 : conc B2}**
  
  ==================================
  exists D3, {G |- D3 : conc (imp B1 B2)}
  
  Subgoal cut.2 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.1>> strengthen H4.
  
  Subgoal cut.1:
  
  Vars: D:(o) -> (o) -> o, B1:o, B2:o, D1:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- impR B1 B2 ([c7]D n c7) : conc (imp B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A, n1:hyp B1 |- D n n1 : conc B2}**
  H7:{G, n1:hyp B1, n:hyp A |- D n n1 : conc B2}**
  H8:{G |- B1 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (imp B1 B2)}
  
  Subgoal cut.2 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.1>> strengthen H5.
  
  Subgoal cut.1:
  
  Vars: D:(o) -> (o) -> o, B1:o, B2:o, D1:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- impR B1 B2 ([c7]D n c7) : conc (imp B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A, n1:hyp B1 |- D n n1 : conc B2}**
  H7:{G, n1:hyp B1, n:hyp A |- D n n1 : conc B2}**
  H8:{G |- B1 : proptm}**
  H9:{G |- B2 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (imp B1 B2)}
  
  Subgoal cut.2 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.1>> weaken H2 with hyp B1.
  
  Subgoal cut.1:
  
  Vars: D:(o) -> (o) -> o, B1:o, B2:o, D1:o, A:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- impR B1 B2 ([c7]D n c7) : conc (imp B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A, n1:hyp B1 |- D n n1 : conc B2}**
  H7:{G, n1:hyp B1, n:hyp A |- D n n1 : conc B2}**
  H8:{G |- B1 : proptm}**
  H9:{G |- B2 : proptm}**
  H10:{G, n2:hyp B1 |- D1 : conc A}
  
  ==================================
  exists D3, {G |- D3 : conc (imp B1 B2)}
  
  Subgoal cut.2 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.1>> apply IH1 to H1 H10 H7 with (G = G,n2:hyp B1), A = A, B = B2, D1 = D1, D2 =
      [x]D x n2.
  
  Subgoal cut.1:
  
  Vars: D3:(o) -> (o) -> (o) -> o, D:(o) -> (o) -> o, B1:o, B2:o, D1:o, A:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- impR B1 B2 ([c7]D n c7) : conc (imp B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A, n1:hyp B1 |- D n n1 : conc B2}**
  H7:{G, n1:hyp B1, n:hyp A |- D n n1 : conc B2}**
  H8:{G |- B1 : proptm}**
  H9:{G |- B2 : proptm}**
  H10:{G, n2:hyp B1 |- D1 : conc A}
  H11:{G, n2:hyp B1 |- D3 n2 n1 n : conc B2}
  
  ==================================
  exists D3, {G |- D3 : conc (imp B1 B2)}
  
  Subgoal cut.2 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.1>> exists impR B1 B2 ([x : o]D3 x n1 n).
  
  Subgoal cut.1:
  
  Vars: D3:(o) -> (o) -> (o) -> o, D:(o) -> (o) -> o, B1:o, B2:o, D1:o, A:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- impR B1 B2 ([c7]D n c7) : conc (imp B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A, n1:hyp B1 |- D n n1 : conc B2}**
  H7:{G, n1:hyp B1, n:hyp A |- D n n1 : conc B2}**
  H8:{G |- B1 : proptm}**
  H9:{G |- B2 : proptm}**
  H10:{G, n2:hyp B1 |- D1 : conc A}
  H11:{G, n2:hyp B1 |- D3 n2 n1 n : conc B2}
  
  ==================================
  {G |- impR B1 B2 ([x]D3 x n1 n) : conc (imp B1 B2)}
  
  Subgoal cut.2 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.1>> search.
  
  Subgoal cut.2:
  
  Vars: A1:(o) -> o, B1:(o) -> o, D3:(o) -> o, D4:(o) -> (o) -> o, D5:(o) -> o,
          D1:o, B:o, A:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:
      {G, n:hyp A |- impL (A1 n) (B1 n) B (D3 n) ([c15]D4 n c15) (D5 n) :
        conc B}@@
  H4:{G, n:hyp A |- A1 n : proptm}**
  H5:{G, n:hyp A |- B1 n : proptm}**
  H6:{G, n:hyp A |- B : proptm}**
  H7:{G, n:hyp A |- D3 n : conc (A1 n)}**
  H8:{G, n:hyp A, n1:hyp (B1 n) |- D4 n n1 : conc B}**
  H9:{G, n:hyp A |- D5 n : hyp (imp (A1 n) (B1 n))}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2>> cases H9.
  
  Subgoal cut.2.1:
  
  Vars: A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o, D1:o, B:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> cases H1.
  
  Subgoal cut.2.1:
  
  Vars: A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o, D1:o, B:o
  Nominals: n1:o, n:o
  Contexts: G{n, n1}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> apply imp_inv to H2.
  
  Subgoal cut.2.1:
  
  Vars: D':(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o,
          D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> apply IH1 to H1 H2 H7 with (G = G), A = imp A2 A3, B = A2, D1 = D1, D2 = D3.
  
  Subgoal cut.2.1:
  
  Vars: D':(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o,
          D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  H13:{G |- D2 n2 n1 n : conc A2}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> apply IH to H10 H13 H12 with (G = G), A = A2, B = A3, D1 = D2 n2 n1 n, D2 =
      [x]D' n1 n x.
  
  Subgoal cut.2.1:
  
  Vars: D':(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o,
          D5:(o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  H13:{G |- D2 n2 n1 n : conc A2}
  H14:{G |- D5 n2 n1 n : conc A3}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> ctxpermute H8 to G,n1:hyp A3,n:hyp imp A2 A3.
  
  Subgoal cut.2.1:
  
  Vars: D':(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o,
          D5:(o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  H13:{G |- D2 n2 n1 n : conc A2}
  H14:{G |- D5 n2 n1 n : conc A3}
  H15:{G, n1:hyp A3, n:hyp (imp A2 A3) |- D4 n n1 : conc B}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> strengthen H5.
  
  Subgoal cut.2.1:
  
  Vars: D':(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o,
          D5:(o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  H13:{G |- D2 n2 n1 n : conc A2}
  H14:{G |- D5 n2 n1 n : conc A3}
  H15:{G, n1:hyp A3, n:hyp (imp A2 A3) |- D4 n n1 : conc B}**
  H16:{G |- A3 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> weaken H2 with hyp A3.
  
  Subgoal cut.2.1:
  
  Vars: D':(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o,
          D5:(o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  H13:{G |- D2 n2 n1 n : conc A2}
  H14:{G |- D5 n2 n1 n : conc A3}
  H15:{G, n1:hyp A3, n:hyp (imp A2 A3) |- D4 n n1 : conc B}**
  H16:{G |- A3 : proptm}**
  H17:{G, n3:hyp A3 |- D1 : conc (imp A2 A3)}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> apply IH1 to H1 H17 H15 with (G = G,n1:hyp A3), A = imp A2 A3, B = B, D1 =
      D1, D2 = [x]D4 x n1.
  
  Subgoal cut.2.1:
  
  Vars: D6:(o) -> (o) -> (o) -> (o) -> o, D':(o) -> (o) -> (o) -> o, A2:o, A3:
          o, D3:(o) -> o, D4:(o) -> (o) -> o, D5:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  H13:{G |- D2 n2 n1 n : conc A2}
  H14:{G |- D5 n2 n1 n : conc A3}
  H15:{G, n1:hyp A3, n:hyp (imp A2 A3) |- D4 n n1 : conc B}**
  H16:{G |- A3 : proptm}**
  H17:{G, n3:hyp A3 |- D1 : conc (imp A2 A3)}
  H18:{G, n1:hyp A3 |- D6 n3 n2 n1 n : conc B}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> apply IH to H11 H14 H18 with (G = G), A = A3, B = B, D1 = D5 n2 n1 n, D2 =
      [x]D6 n3 n2 x n.
  
  Subgoal cut.2.1:
  
  Vars: D7:(o) -> (o) -> (o) -> (o) -> o, D6:(o) -> (o) -> (o) -> (o) -> o, D':
          (o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o,
          D5:(o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  H13:{G |- D2 n2 n1 n : conc A2}
  H14:{G |- D5 n2 n1 n : conc A3}
  H15:{G, n1:hyp A3, n:hyp (imp A2 A3) |- D4 n n1 : conc B}**
  H16:{G |- A3 : proptm}**
  H17:{G, n3:hyp A3 |- D1 : conc (imp A2 A3)}
  H18:{G, n1:hyp A3 |- D6 n3 n2 n1 n : conc B}
  H19:{G |- D7 n3 n2 n1 n : conc B}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> exists D7 n3 n2 n1 n.
  
  Subgoal cut.2.1:
  
  Vars: D7:(o) -> (o) -> (o) -> (o) -> o, D6:(o) -> (o) -> (o) -> (o) -> o, D':
          (o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> o, D4:(o) -> (o) -> o,
          D5:(o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{imp A2 A3 : proptm}@
  H2:{G |- D1 : conc (imp A2 A3)}
  H3:{G, n:hyp (imp A2 A3) |- impL A2 A3 B (D3 n) ([c15]D4 n c15) n : conc B}@@
  H4:{G, n:hyp (imp A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (imp A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (imp A2 A3) |- B : proptm}**
  H7:{G, n:hyp (imp A2 A3) |- D3 n : conc A2}**
  H8:{G, n:hyp (imp A2 A3), n1:hyp A3 |- D4 n n1 : conc B}**
  H9:{G, n:hyp (imp A2 A3) |- n : hyp (imp A2 A3)}**
  H10:{A2 : proptm}*
  H11:{A3 : proptm}*
  H12:{G, n2:hyp A2 |- D' n1 n n2 : conc A3}
  H13:{G |- D2 n2 n1 n : conc A2}
  H14:{G |- D5 n2 n1 n : conc A3}
  H15:{G, n1:hyp A3, n:hyp (imp A2 A3) |- D4 n n1 : conc B}**
  H16:{G |- A3 : proptm}**
  H17:{G, n3:hyp A3 |- D1 : conc (imp A2 A3)}
  H18:{G, n1:hyp A3 |- D6 n3 n2 n1 n : conc B}
  H19:{G |- D7 n3 n2 n1 n : conc B}
  
  ==================================
  {G |- D7 n3 n2 n1 n : conc B}
  
  Subgoal cut.2.2 is:
   exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.1>> search.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> apply IH1 to H1 H2 H7 with (G = G), A = A n2, B = A3 n2, D1 = D1 n2, D2 =
      [x]D3 n2 x.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:(o) -> o, B:
          (o) -> o, A:(o) -> o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> ctxpermute H8 to G,n1:hyp A4 n2,n:hyp A n2.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:(o) -> o, B:
          (o) -> o, A:(o) -> o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  H11:{G, n1:hyp (A4 n2), n:hyp (A n2) |- D4 n2 n n1 : conc (B n2)}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> strengthen H5.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:(o) -> o, B:
          (o) -> o, A:(o) -> o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  H11:{G, n1:hyp (A4 n2), n:hyp (A n2) |- D4 n2 n n1 : conc (B n2)}**
  H12:{G |- A4 n2 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> weaken H2 with hyp A4 n2.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:(o) -> o, B:
          (o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n3}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  H11:{G, n1:hyp (A4 n2), n:hyp (A n2) |- D4 n2 n n1 : conc (B n2)}**
  H12:{G |- A4 n2 : proptm}**
  H13:{G, n3:hyp (A4 n2) |- D1 n2 : conc (A n2)}
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> apply IH1 to H1 H13 H11 with (G = G,n1:hyp A4 n2), A = A n2, B = B n2, D1 =
      D1 n2, D2 = [x]D4 n2 x n1.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D5:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n3}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  H11:{G, n1:hyp (A4 n2), n:hyp (A n2) |- D4 n2 n n1 : conc (B n2)}**
  H12:{G |- A4 n2 : proptm}**
  H13:{G, n3:hyp (A4 n2) |- D1 n2 : conc (A n2)}
  H14:{G, n1:hyp (A4 n2) |- D5 n3 n2 n1 n : conc (B n2)}
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> strengthen H4.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D5:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n3}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  H11:{G, n1:hyp (A4 n2), n:hyp (A n2) |- D4 n2 n n1 : conc (B n2)}**
  H12:{G |- A4 n2 : proptm}**
  H13:{G, n3:hyp (A4 n2) |- D1 n2 : conc (A n2)}
  H14:{G, n1:hyp (A4 n2) |- D5 n3 n2 n1 n : conc (B n2)}
  H15:{G |- A3 n2 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> strengthen H5.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D5:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n3}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  H11:{G, n1:hyp (A4 n2), n:hyp (A n2) |- D4 n2 n n1 : conc (B n2)}**
  H12:{G |- A4 n2 : proptm}**
  H13:{G, n3:hyp (A4 n2) |- D1 n2 : conc (A n2)}
  H14:{G, n1:hyp (A4 n2) |- D5 n3 n2 n1 n : conc (B n2)}
  H15:{G |- A3 n2 : proptm}**
  H16:{G |- A4 n2 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> strengthen H6.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D5:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n3}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  H11:{G, n1:hyp (A4 n2), n:hyp (A n2) |- D4 n2 n n1 : conc (B n2)}**
  H12:{G |- A4 n2 : proptm}**
  H13:{G, n3:hyp (A4 n2) |- D1 n2 : conc (A n2)}
  H14:{G, n1:hyp (A4 n2) |- D5 n3 n2 n1 n : conc (B n2)}
  H15:{G |- A3 n2 : proptm}**
  H16:{G |- A4 n2 : proptm}**
  H17:{G |- B n2 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> exists impL A3 n2 A4 n2 B n2 D2 n2 n1 n ([x]D5 n3 n2 x n) n2.
  
  Subgoal cut.2.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D5:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n3}:c[(n2:hyp (imp (A3 n2) (A4 n2)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n2 : proptm}@
  H2:{G |- D1 n2 : conc (A n2)}
  H3:
      {G, n:hyp (A n2) |- 
        impL (A3 n2) (A4 n2) (B n2) (D3 n2 n) ([c15]D4 n2 n c15) n2 :
        conc (B n2)}@@
  H4:{G, n:hyp (A n2) |- A3 n2 : proptm}**
  H5:{G, n:hyp (A n2) |- A4 n2 : proptm}**
  H6:{G, n:hyp (A n2) |- B n2 : proptm}**
  H7:{G, n:hyp (A n2) |- D3 n2 n : conc (A3 n2)}**
  H8:{G, n:hyp (A n2), n1:hyp (A4 n2) |- D4 n2 n n1 : conc (B n2)}**
  H9:{G, n:hyp (A n2) |- n2 : hyp (imp (A3 n2) (A4 n2))}**
  H10:{G |- D2 n2 n1 n : conc (A3 n2)}
  H11:{G, n1:hyp (A4 n2), n:hyp (A n2) |- D4 n2 n n1 : conc (B n2)}**
  H12:{G |- A4 n2 : proptm}**
  H13:{G, n3:hyp (A4 n2) |- D1 n2 : conc (A n2)}
  H14:{G, n1:hyp (A4 n2) |- D5 n3 n2 n1 n : conc (B n2)}
  H15:{G |- A3 n2 : proptm}**
  H16:{G |- A4 n2 : proptm}**
  H17:{G |- B n2 : proptm}**
  
  ==================================
  {G |- impL (A3 n2) (A4 n2) (B n2) (D2 n2 n1 n) ([x]D5 n3 n2 x n) n2 :
    conc (B n2)}
  
  Subgoal cut.3 is:
   exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.2.2>> search.
  
  Subgoal cut.3:
  
  Vars: D3:(o) -> o, D4:(o) -> o, B1:o, B2:o, D1:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- andR B1 B2 (D3 n) (D4 n) : conc (and B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A |- D3 n : conc B1}**
  H7:{G, n:hyp A |- D4 n : conc B2}**
  
  ==================================
  exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.3>> apply IH1 to H1 H2 H6 with A = A, B = B1, D1 = D1, D2 = D3.
  
  Subgoal cut.3:
  
  Vars: D3:(o) -> o, D4:(o) -> o, B1:o, B2:o, D2:(o) -> o, D1:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- andR B1 B2 (D3 n) (D4 n) : conc (and B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A |- D3 n : conc B1}**
  H7:{G, n:hyp A |- D4 n : conc B2}**
  H8:{G |- D2 n : conc B1}
  
  ==================================
  exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.3>> apply IH1 to H1 H2 H7 with A = A, B = B2, D1 = D1, D2 = D4.
  
  Subgoal cut.3:
  
  Vars: D5:(o) -> o, D3:(o) -> o, D4:(o) -> o, B1:o, B2:o, D2:(o) -> o, D1:o, A
          :o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- andR B1 B2 (D3 n) (D4 n) : conc (and B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A |- D3 n : conc B1}**
  H7:{G, n:hyp A |- D4 n : conc B2}**
  H8:{G |- D2 n : conc B1}
  H9:{G |- D5 n : conc B2}
  
  ==================================
  exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.3>> strengthen H4.
  
  Subgoal cut.3:
  
  Vars: D5:(o) -> o, D3:(o) -> o, D4:(o) -> o, B1:o, B2:o, D2:(o) -> o, D1:o, A
          :o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- andR B1 B2 (D3 n) (D4 n) : conc (and B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A |- D3 n : conc B1}**
  H7:{G, n:hyp A |- D4 n : conc B2}**
  H8:{G |- D2 n : conc B1}
  H9:{G |- D5 n : conc B2}
  H10:{G |- B1 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.3>> strengthen H5.
  
  Subgoal cut.3:
  
  Vars: D5:(o) -> o, D3:(o) -> o, D4:(o) -> o, B1:o, B2:o, D2:(o) -> o, D1:o, A
          :o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- andR B1 B2 (D3 n) (D4 n) : conc (and B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A |- D3 n : conc B1}**
  H7:{G, n:hyp A |- D4 n : conc B2}**
  H8:{G |- D2 n : conc B1}
  H9:{G |- D5 n : conc B2}
  H10:{G |- B1 : proptm}**
  H11:{G |- B2 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.3>> exists andR B1 B2 D2 n D5 n.
  
  Subgoal cut.3:
  
  Vars: D5:(o) -> o, D3:(o) -> o, D4:(o) -> o, B1:o, B2:o, D2:(o) -> o, D1:o, A
          :o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- andR B1 B2 (D3 n) (D4 n) : conc (and B1 B2)}@@
  H4:{G, n:hyp A |- B1 : proptm}**
  H5:{G, n:hyp A |- B2 : proptm}**
  H6:{G, n:hyp A |- D3 n : conc B1}**
  H7:{G, n:hyp A |- D4 n : conc B2}**
  H8:{G |- D2 n : conc B1}
  H9:{G |- D5 n : conc B2}
  H10:{G |- B1 : proptm}**
  H11:{G |- B2 : proptm}**
  
  ==================================
  {G |- andR B1 B2 (D2 n) (D5 n) : conc (and B1 B2)}
  
  Subgoal cut.4 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.3>> search.
  
  Subgoal cut.4:
  
  Vars: A1:(o) -> o, B1:(o) -> o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> o, D1:o,
          B:o, A:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:
      {G, n:hyp A |- andL (A1 n) (B1 n) B ([c29][c30]D3 n c29 c30) (D4 n) :
        conc B}@@
  H4:{G, n:hyp A |- A1 n : proptm}**
  H5:{G, n:hyp A |- B1 n : proptm}**
  H6:{G, n:hyp A |- B : proptm}**
  H7:{G, n:hyp A, n1:hyp (A1 n), n2:hyp (B1 n) |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp A |- D4 n : hyp (and (A1 n) (B1 n))}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4>> cases H8.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> cases H1.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> apply and_inv to H2.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H11:{G |- D2 n2 n1 n : conc A2} /\ {G |- D4 n2 n1 n : conc A3}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> cases H11.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> ctxpermute H7 to G,n1:hyp A2,n2:hyp A3,n:hyp and A2 A3.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> assert {G,n1:hyp A2,n2:hyp A3 |- D1 : conc and A2 A3}.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  
  ==================================
  {G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> strengthen H4.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G |- A2 : proptm}**
  
  ==================================
  {G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> strengthen H5.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G |- A2 : proptm}**
  H16:{G |- A3 : proptm}**
  
  ==================================
  {G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> weaken H2 with hyp A2.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G |- A2 : proptm}**
  H16:{G |- A3 : proptm}**
  H17:{G, n3:hyp A2 |- D1 : conc (and A2 A3)}
  
  ==================================
  {G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> weaken H16 with hyp A2.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G |- A2 : proptm}**
  H16:{G |- A3 : proptm}**
  H17:{G, n3:hyp A2 |- D1 : conc (and A2 A3)}
  H18:{G, n4:hyp A2 |- A3 : proptm}**
  
  ==================================
  {G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> weaken H17 with hyp A3.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4, n5}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G |- A2 : proptm}**
  H16:{G |- A3 : proptm}**
  H17:{G, n3:hyp A2 |- D1 : conc (and A2 A3)}
  H18:{G, n4:hyp A2 |- A3 : proptm}**
  H19:{G, n3:hyp A2, n5:hyp A3 |- D1 : conc (and A2 A3)}
  
  ==================================
  {G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> search.
  
  Subgoal cut.4.1:
  
  Vars: A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> apply IH1 to H1 H15 H14 with (G = G,n1:hyp A2,n2:hyp A3), A = and A2 A3, B =
      B, D1 = D1, D2 = [x]D3 x n1 n2.
  
  Subgoal cut.4.1:
  
  Vars: D5:(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  H16:{G, n1:hyp A2, n2:hyp A3 |- D5 n2 n1 n : conc B}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> assert {G |- [x]D4 n2 n1 n : {x:hyp A2}conc A3}.
  
  Subgoal cut.4.1:
  
  Vars: D5:(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  H16:{G, n1:hyp A2, n2:hyp A3 |- D5 n2 n1 n : conc B}
  
  ==================================
  {G, n3:hyp A2 |- D4 n2 n1 n : conc A3}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> strengthen H4.
  
  Subgoal cut.4.1:
  
  Vars: D5:(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  H16:{G, n1:hyp A2, n2:hyp A3 |- D5 n2 n1 n : conc B}
  H17:{G |- A2 : proptm}**
  
  ==================================
  {G, n3:hyp A2 |- D4 n2 n1 n : conc A3}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> weaken H13 with hyp A2.
  
  Subgoal cut.4.1:
  
  Vars: D5:(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3, n4}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  H16:{G, n1:hyp A2, n2:hyp A3 |- D5 n2 n1 n : conc B}
  H17:{G |- A2 : proptm}**
  H18:{G, n4:hyp A2 |- D4 n2 n1 n : conc A3}
  
  ==================================
  {G, n3:hyp A2 |- D4 n2 n1 n : conc A3}
  
  Subgoal cut.4.1 is:
   exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> search.
  
  Subgoal cut.4.1:
  
  Vars: D5:(o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  H16:{G, n1:hyp A2, n2:hyp A3 |- D5 n2 n1 n : conc B}
  H17:{G, n3:hyp A2 |- D4 n2 n1 n : conc A3}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> apply IH to H10 H17 H16 with (G = G,n1:hyp A2), A = A3, B = B, D2 =
      [x]D5 x n1 n.
  
  Subgoal cut.4.1:
  
  Vars: D6:(o) -> (o) -> (o) -> (o) -> o, D5:(o) -> (o) -> (o) -> o, A2:o, A3:
          o, D3:(o) -> (o) -> (o) -> o, D4:(o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  H16:{G, n1:hyp A2, n2:hyp A3 |- D5 n2 n1 n : conc B}
  H17:{G, n3:hyp A2 |- D4 n2 n1 n : conc A3}
  H18:{G, n1:hyp A2 |- D6 n3 n2 n1 n : conc B}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> apply IH to H9 H12 H18.
  
  Subgoal cut.4.1:
  
  Vars: D7:(o) -> (o) -> (o) -> (o) -> o, D6:(o) -> (o) -> (o) -> (o) -> o, D5:
          (o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  H16:{G, n1:hyp A2, n2:hyp A3 |- D5 n2 n1 n : conc B}
  H17:{G, n3:hyp A2 |- D4 n2 n1 n : conc A3}
  H18:{G, n1:hyp A2 |- D6 n3 n2 n1 n : conc B}
  H19:{G |- D7 n3 n2 n1 n : conc B}
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> exists D7 n3 n2 n1 n.
  
  Subgoal cut.4.1:
  
  Vars: D7:(o) -> (o) -> (o) -> (o) -> o, D6:(o) -> (o) -> (o) -> (o) -> o, D5:
          (o) -> (o) -> (o) -> o, A2:o, A3:o, D3:(o) -> (o) -> (o) -> o, D4:
          (o) -> (o) -> (o) -> o, D2:(o) -> (o) -> (o) -> o, D1:o, B:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n3}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{and A2 A3 : proptm}@
  H2:{G |- D1 : conc (and A2 A3)}
  H3:
      {G, n:hyp (and A2 A3) |- andL A2 A3 B ([c29][c30]D3 n c29 c30) n :
        conc B}@@
  H4:{G, n:hyp (and A2 A3) |- A2 : proptm}**
  H5:{G, n:hyp (and A2 A3) |- A3 : proptm}**
  H6:{G, n:hyp (and A2 A3) |- B : proptm}**
  H7:{G, n:hyp (and A2 A3), n1:hyp A2, n2:hyp A3 |- D3 n n1 n2 : conc B}**
  H8:{G, n:hyp (and A2 A3) |- n : hyp (and A2 A3)}**
  H9:{A2 : proptm}*
  H10:{A3 : proptm}*
  H12:{G |- D2 n2 n1 n : conc A2}
  H13:{G |- D4 n2 n1 n : conc A3}
  H14:{G, n1:hyp A2, n2:hyp A3, n:hyp (and A2 A3) |- D3 n n1 n2 : conc B}**
  H15:{G, n1:hyp A2, n2:hyp A3 |- D1 : conc (and A2 A3)}
  H16:{G, n1:hyp A2, n2:hyp A3 |- D5 n2 n1 n : conc B}
  H17:{G, n3:hyp A2 |- D4 n2 n1 n : conc A3}
  H18:{G, n1:hyp A2 |- D6 n3 n2 n1 n : conc B}
  H19:{G |- D7 n3 n2 n1 n : conc B}
  
  ==================================
  {G |- D7 n3 n2 n1 n : conc B}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.1>> search.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> ctxpermute H7 to G,n1:hyp A3 n3,n2:hyp A4 n3,n:hyp A n3.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> assert {G,n1:hyp A3 n3,n2:hyp A4 n3 |- D1 n3 : conc A n3}.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  
  ==================================
  {G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> strengthen H4.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G |- A3 n3 : proptm}**
  
  ==================================
  {G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> strengthen H5.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G |- A3 n3 : proptm}**
  H11:{G |- A4 n3 : proptm}**
  
  ==================================
  {G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> weaken H2 with hyp A3 n3.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n4}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G |- A3 n3 : proptm}**
  H11:{G |- A4 n3 : proptm}**
  H12:{G, n4:hyp (A3 n3) |- D1 n3 : conc (A n3)}
  
  ==================================
  {G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> weaken H11 with hyp A3 n3.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n4, n5}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G |- A3 n3 : proptm}**
  H11:{G |- A4 n3 : proptm}**
  H12:{G, n4:hyp (A3 n3) |- D1 n3 : conc (A n3)}
  H13:{G, n5:hyp (A3 n3) |- A4 n3 : proptm}**
  
  ==================================
  {G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> weaken H12 with hyp A4 n3.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2, n4, n5, n6}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G |- A3 n3 : proptm}**
  H11:{G |- A4 n3 : proptm}**
  H12:{G, n4:hyp (A3 n3) |- D1 n3 : conc (A n3)}
  H13:{G, n5:hyp (A3 n3) |- A4 n3 : proptm}**
  H14:{G, n4:hyp (A3 n3), n6:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  
  ==================================
  {G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  
  Subgoal cut.4.2 is:
   exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> search.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  
  ==================================
  exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> apply IH1 to H1 H10 H9 with (G = G,n1:hyp A3 n3,n2:hyp A4 n3), A = A n3, B =
      B n3, D1 = D1 n3, D2 = [x]D3 n3 x n1 n2.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  H11:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D2 n3 n2 n1 n : conc (B n3)}
  
  ==================================
  exists D3, {G |- D3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> exists andL A3 n3 A4 n3 B n3 ([x][y]D2 n3 y x n) n3.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  H11:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D2 n3 n2 n1 n : conc (B n3)}
  
  ==================================
  {G |- andL (A3 n3) (A4 n3) (B n3) ([x][y]D2 n3 y x n) n3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> strengthen H4.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  H11:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D2 n3 n2 n1 n : conc (B n3)}
  H12:{G |- A3 n3 : proptm}**
  
  ==================================
  {G |- andL (A3 n3) (A4 n3) (B n3) ([x][y]D2 n3 y x n) n3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> strengthen H5.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  H11:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D2 n3 n2 n1 n : conc (B n3)}
  H12:{G |- A3 n3 : proptm}**
  H13:{G |- A4 n3 : proptm}**
  
  ==================================
  {G |- andL (A3 n3) (A4 n3) (B n3) ([x][y]D2 n3 y x n) n3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> strengthen H6.
  
  Subgoal cut.4.2:
  
  Vars: A3:(o) -> o, A4:(o) -> o, D3:(o) -> (o) -> (o) -> (o) -> o, D2:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: G{n, n1, n2}:c[(n3:hyp (and (A3 n3) (A4 n3)))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n3 : proptm}@
  H2:{G |- D1 n3 : conc (A n3)}
  H3:
      {G, n:hyp (A n3) |- 
        andL (A3 n3) (A4 n3) (B n3) ([c29][c30]D3 n3 n c29 c30) n3 :
        conc (B n3)}@@
  H4:{G, n:hyp (A n3) |- A3 n3 : proptm}**
  H5:{G, n:hyp (A n3) |- A4 n3 : proptm}**
  H6:{G, n:hyp (A n3) |- B n3 : proptm}**
  H7:
      {G, n:hyp (A n3), n1:hyp (A3 n3), n2:hyp (A4 n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H8:{G, n:hyp (A n3) |- n3 : hyp (and (A3 n3) (A4 n3))}**
  H9:
      {G, n1:hyp (A3 n3), n2:hyp (A4 n3), n:hyp (A n3) |- D3 n3 n n1 n2 :
        conc (B n3)}**
  H10:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D1 n3 : conc (A n3)}
  H11:{G, n1:hyp (A3 n3), n2:hyp (A4 n3) |- D2 n3 n2 n1 n : conc (B n3)}
  H12:{G |- A3 n3 : proptm}**
  H13:{G |- A4 n3 : proptm}**
  H14:{G |- B n3 : proptm}**
  
  ==================================
  {G |- andL (A3 n3) (A4 n3) (B n3) ([x][y]D2 n3 y x n) n3 : conc (B n3)}
  
  Subgoal cut.5 is:
   exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.4.2>> search.
  
  Subgoal cut.5:
  
  Vars: D1:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- topR : conc top}@@
  
  ==================================
  exists D3, {G |- D3 : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.5>> exists topR.
  
  Subgoal cut.5:
  
  Vars: D1:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- topR : conc top}@@
  
  ==================================
  {G |- topR : conc top}
  
  Subgoal cut.6 is:
   exists D3, {G |- D3 : conc B}
  
  cut.5>> search.
  
  Subgoal cut.6:
  
  Vars: D:(o) -> o, D1:o, B:o, A:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A : proptm}@
  H2:{G |- D1 : conc A}
  H3:{G, n:hyp A |- init B (D n) : conc B}@@
  H4:{G, n:hyp A |- B : proptm}**
  H5:{G, n:hyp A |- D n : hyp B}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  cut.6>> cases H5.
  
  Subgoal cut.6.1:
  
  Vars: D1:o, B:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{B : proptm}@
  H2:{G |- D1 : conc B}
  H3:{G, n:hyp B |- init B n : conc B}@@
  H4:{G, n:hyp B |- B : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc B}
  
  Subgoal cut.6.2 is:
   exists D3, {G |- D3 : conc (B n1)}
  
  cut.6.1>> exists D1.
  
  Subgoal cut.6.1:
  
  Vars: D1:o, B:o
  Nominals: n:o
  Contexts: G{n}:c[]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{B : proptm}@
  H2:{G |- D1 : conc B}
  H3:{G, n:hyp B |- init B n : conc B}@@
  H4:{G, n:hyp B |- B : proptm}**
  
  ==================================
  {G |- D1 : conc B}
  
  Subgoal cut.6.2 is:
   exists D3, {G |- D3 : conc (B n1)}
  
  cut.6.1>> search.
  
  Subgoal cut.6.2:
  
  Vars: D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n}:c[(n1:hyp (B n1))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n1 : proptm}@
  H2:{G |- D1 n1 : conc (A n1)}
  H3:{G, n:hyp (A n1) |- init (B n1) n1 : conc (B n1)}@@
  H4:{G, n:hyp (A n1) |- B n1 : proptm}**
  
  ==================================
  exists D3, {G |- D3 : conc (B n1)}
  
  cut.6.2>> strengthen H3.
  
  Subgoal cut.6.2:
  
  Vars: D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n}:c[(n1:hyp (B n1))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n1 : proptm}@
  H2:{G |- D1 n1 : conc (A n1)}
  H3:{G, n:hyp (A n1) |- init (B n1) n1 : conc (B n1)}@@
  H4:{G, n:hyp (A n1) |- B n1 : proptm}**
  H6:{G |- init (B n1) n1 : conc (B n1)}@@
  
  ==================================
  exists D3, {G |- D3 : conc (B n1)}
  
  cut.6.2>> exists init B n1 n1.
  
  Subgoal cut.6.2:
  
  Vars: D1:(o) -> o, B:(o) -> o, A:(o) -> o
  Nominals: n1:o, n:o
  Contexts: G{n}:c[(n1:hyp (B n1))]
  IH:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}* =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B} =>
                      exists D3, {G |- D3 : conc B}
  IH1:
      ctx G:c.
        forall A, forall B, forall D1, forall D2,
          {A : proptm}@ =>
              {G |- D1 : conc A} =>
                  {G |- [x]D2 x : {x:hyp A}conc B}** =>
                      exists D3, {G |- D3 : conc B}
  H1:{A n1 : proptm}@
  H2:{G |- D1 n1 : conc (A n1)}
  H3:{G, n:hyp (A n1) |- init (B n1) n1 : conc (B n1)}@@
  H4:{G, n:hyp (A n1) |- B n1 : proptm}**
  H6:{G |- init (B n1) n1 : conc (B n1)}@@
  
  ==================================
  {G |- init (B n1) n1 : conc (B n1)}
  
  cut.6.2>> search.
  Proof Completed!
  
  >> Goodbye!
