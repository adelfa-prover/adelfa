  $ adelfa -i lists.ath
  Welcome!
  >> Specification "lists.lf".
  
  >> Theorem Lemma1:
      forall  L1 L2 L3 L4 D1 D2,
        {D1 : rev_acc L1 L2 L3} =>
          {D2 : rev_acc L1 L2 L4} => exists  D3, {D3 : eq_list L3 L4}.
  
  Subgoal Lemma1:
  
  
  ==================================
  forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
    {D1 : rev_acc L1 L2 L3} =>
        {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  
  Lemma1>> induction on 1.
  
  Subgoal Lemma1:
  
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  
  ==================================
  forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
    {D1 : rev_acc L1 L2 L3}@ =>
        {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  
  Lemma1>> intros.
  
  Subgoal Lemma1:
  
  Vars: D2:o, D1:o, L4:o, L3:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H1:{D1 : rev_acc L1 L2 L3}@
  H2:{D2 : rev_acc L1 L2 L4}
  
  ==================================
  exists D3, {D3 : eq_list L3 L4}
  
  Lemma1>> cases H1.
  
  Subgoal Lemma1.1:
  
  Vars: D:o, N:o, L5:o, D2:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H2:{D2 : rev_acc (cons N L5) L2 L4}
  H3:{L5 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L5 (cons N L2) L3}*
  
  ==================================
  exists D3, {D3 : eq_list L3 L4}
  
  Subgoal Lemma1.2 is:
   exists D3, {D3 : eq_list L3 L4}
  
  Lemma1.1>> cases H2.
  
  Subgoal Lemma1.1:
  
  Vars: D3:o, D:o, N:o, L5:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H3:{L5 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L5 (cons N L2) L3}*
  H8:{L5 : list}
  H9:{L2 : list}
  H10:{L4 : list}
  H11:{N : nat}
  H12:{D3 : rev_acc L5 (cons N L2) L4}
  
  ==================================
  exists D3, {D3 : eq_list L3 L4}
  
  Subgoal Lemma1.2 is:
   exists D3, {D3 : eq_list L3 L4}
  
  Lemma1.1>> apply IH to H7 H12 with L1 = L5, L2 = cons N L2, L3 = L3, L4 = L4, D1 = D, D2
      = D3.
  
  Subgoal Lemma1.1:
  
  Vars: D3:o, D:o, N:o, L5:o, D1:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H3:{L5 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L5 (cons N L2) L3}*
  H8:{L5 : list}
  H9:{L2 : list}
  H10:{L4 : list}
  H11:{N : nat}
  H12:{D3 : rev_acc L5 (cons N L2) L4}
  H13:{D1 : eq_list L3 L4}
  
  ==================================
  exists D3, {D3 : eq_list L3 L4}
  
  Subgoal Lemma1.2 is:
   exists D3, {D3 : eq_list L3 L4}
  
  Lemma1.1>> exists D1.
  
  Subgoal Lemma1.1:
  
  Vars: D3:o, D:o, N:o, L5:o, D1:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H3:{L5 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L5 (cons N L2) L3}*
  H8:{L5 : list}
  H9:{L2 : list}
  H10:{L4 : list}
  H11:{N : nat}
  H12:{D3 : rev_acc L5 (cons N L2) L4}
  H13:{D1 : eq_list L3 L4}
  
  ==================================
  {D1 : eq_list L3 L4}
  
  Subgoal Lemma1.2 is:
   exists D3, {D3 : eq_list L3 L4}
  
  Lemma1.1>> search.
  
  Subgoal Lemma1.2:
  
  Vars: D2:o, L4:o, L3:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H2:{D2 : rev_acc nil L3 L4}
  H3:{L3 : list}*
  
  ==================================
  exists D3, {D3 : eq_list L3 L4}
  
  Lemma1.2>> cases H2.
  
  Subgoal Lemma1.2:
  
  Vars: L4:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H3:{L4 : list}*
  H4:{L4 : list}
  
  ==================================
  exists D3, {D3 : eq_list L4 L4}
  
  Lemma1.2>> exists refl_list L4.
  
  Subgoal Lemma1.2:
  
  Vars: L4:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H3:{L4 : list}*
  H4:{L4 : list}
  
  ==================================
  {refl_list L4 : eq_list L4 L4}
  
  Lemma1.2>> search.
  Proof Completed!
  
  >> Theorem Lemma2:
      forall  a B AB ba ba2 D1 D2 D3,
        {D1 : rev_acc a B AB} =>
          {D2 : rev_acc AB nil ba} =>
            {D3 : rev_acc B a ba2} => exists  D4, {D4 : eq_list ba ba2}.
  
  Subgoal Lemma2:
  
  
  ==================================
  forall a, forall B, forall AB, forall ba, forall ba2, forall D1, forall D2,
    forall D3,
    {D1 : rev_acc a B AB} =>
        {D2 : rev_acc AB nil ba} =>
            {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  
  Lemma2>> induction on 1.
  
  Subgoal Lemma2:
  
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  
  ==================================
  forall a, forall B, forall AB, forall ba, forall ba2, forall D1, forall D2,
    forall D3,
    {D1 : rev_acc a B AB}@ =>
        {D2 : rev_acc AB nil ba} =>
            {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  
  Lemma2>> intros.
  
  Subgoal Lemma2:
  
  Vars: D3:o, D2:o, D1:o, ba2:o, ba:o, AB:o, B:o, a:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H1:{D1 : rev_acc a B AB}@
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc B a ba2}
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Lemma2>> cases H1.
  
  Subgoal Lemma2.1:
  
  Vars: D:o, N:o, L1:o, D3:o, D2:o, ba2:o, ba:o, AB:o, B:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc B (cons N L1) ba2}
  H4:{L1 : list}*
  H5:{B : list}*
  H6:{AB : list}*
  H7:{N : nat}*
  H8:{D : rev_acc L1 (cons N B) AB}*
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Subgoal Lemma2.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.1>> assert {ba2 : list}.
  
  Subgoal Lemma2.1:
  
  Vars: D:o, N:o, L1:o, D3:o, D2:o, ba2:o, ba:o, AB:o, B:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc B (cons N L1) ba2}
  H4:{L1 : list}*
  H5:{B : list}*
  H6:{AB : list}*
  H7:{N : nat}*
  H8:{D : rev_acc L1 (cons N B) AB}*
  H9:{ba2 : list}
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Subgoal Lemma2.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.1>> assert exists  D4, {D4 : rev_acc cons N B L1 ba2}.
  
  Subgoal Lemma2.1:
  
  Vars: D:o, N:o, L1:o, D3:o, D2:o, ba2:o, ba:o, AB:o, B:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc B (cons N L1) ba2}
  H4:{L1 : list}*
  H5:{B : list}*
  H6:{AB : list}*
  H7:{N : nat}*
  H8:{D : rev_acc L1 (cons N B) AB}*
  H9:{ba2 : list}
  
  ==================================
  exists D4, {D4 : rev_acc (cons N B) L1 ba2}
  
  Subgoal Lemma2.1 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Subgoal Lemma2.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.1>> exists rev_acc_cons B L1 ba2 N D3.
  
  Subgoal Lemma2.1:
  
  Vars: D:o, N:o, L1:o, D3:o, D2:o, ba2:o, ba:o, AB:o, B:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc B (cons N L1) ba2}
  H4:{L1 : list}*
  H5:{B : list}*
  H6:{AB : list}*
  H7:{N : nat}*
  H8:{D : rev_acc L1 (cons N B) AB}*
  H9:{ba2 : list}
  
  ==================================
  {rev_acc_cons B L1 ba2 N D3 : rev_acc (cons N B) L1 ba2}
  
  Subgoal Lemma2.1 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Subgoal Lemma2.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.1>> search.
  
  Subgoal Lemma2.1:
  
  Vars: D4:o, D:o, N:o, L1:o, D3:o, D2:o, ba2:o, ba:o, AB:o, B:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc B (cons N L1) ba2}
  H4:{L1 : list}*
  H5:{B : list}*
  H6:{AB : list}*
  H7:{N : nat}*
  H8:{D : rev_acc L1 (cons N B) AB}*
  H9:{ba2 : list}
  H10:{D4 : rev_acc (cons N B) L1 ba2}
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Subgoal Lemma2.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.1>> apply IH to H8 H2 H10 with a = L1, B = cons N B, AB = AB, ba = ba, ba2 = ba2,
      D1 = D, D2 = D2, D3 = D4.
  
  Subgoal Lemma2.1:
  
  Vars: D4:o, D:o, N:o, L1:o, D3:o, D2:o, D1:o, ba2:o, ba:o, AB:o, B:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc B (cons N L1) ba2}
  H4:{L1 : list}*
  H5:{B : list}*
  H6:{AB : list}*
  H7:{N : nat}*
  H8:{D : rev_acc L1 (cons N B) AB}*
  H9:{ba2 : list}
  H10:{D4 : rev_acc (cons N B) L1 ba2}
  H11:{D1 : eq_list ba ba2}
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Subgoal Lemma2.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.1>> cases H11.
  
  Subgoal Lemma2.1:
  
  Vars: D4:o, D:o, N:o, L1:o, D3:o, D2:o, ba2:o, AB:o, B:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba2}
  H3:{D3 : rev_acc B (cons N L1) ba2}
  H4:{L1 : list}*
  H5:{B : list}*
  H6:{AB : list}*
  H7:{N : nat}*
  H8:{D : rev_acc L1 (cons N B) AB}*
  H9:{ba2 : list}
  H10:{D4 : rev_acc (cons N B) L1 ba2}
  H12:{ba2 : list}
  
  ==================================
  exists D4, {D4 : eq_list ba2 ba2}
  
  Subgoal Lemma2.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.1>> exists refl_list ba2.
  
  Subgoal Lemma2.1:
  
  Vars: D4:o, D:o, N:o, L1:o, D3:o, D2:o, ba2:o, AB:o, B:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba2}
  H3:{D3 : rev_acc B (cons N L1) ba2}
  H4:{L1 : list}*
  H5:{B : list}*
  H6:{AB : list}*
  H7:{N : nat}*
  H8:{D : rev_acc L1 (cons N B) AB}*
  H9:{ba2 : list}
  H10:{D4 : rev_acc (cons N B) L1 ba2}
  H12:{ba2 : list}
  
  ==================================
  {refl_list ba2 : eq_list ba2 ba2}
  
  Subgoal Lemma2.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.1>> search.
  
  Subgoal Lemma2.2:
  
  Vars: D3:o, D2:o, ba2:o, ba:o, AB:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc AB nil ba2}
  H4:{AB : list}*
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.2>> apply Lemma1 to H2 H3 with L1 = AB, L2 = nil, L3 = ba, L4 = ba2, D1 = D2, D2
      = D3.
  
  Subgoal Lemma2.2:
  
  Vars: D3:o, D2:o, D1:o, ba2:o, ba:o, AB:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc AB nil ba2}
  H4:{AB : list}*
  H5:{D1 : eq_list ba ba2}
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Lemma2.2>> exists D1.
  
  Subgoal Lemma2.2:
  
  Vars: D3:o, D2:o, D1:o, ba2:o, ba:o, AB:o
  IH:
      forall a, forall B, forall AB, forall ba, forall ba2, forall D1,
        forall D2, forall D3,
        {D1 : rev_acc a B AB}* =>
            {D2 : rev_acc AB nil ba} =>
                {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  H2:{D2 : rev_acc AB nil ba}
  H3:{D3 : rev_acc AB nil ba2}
  H4:{AB : list}*
  H5:{D1 : eq_list ba ba2}
  
  ==================================
  {D1 : eq_list ba ba2}
  
  Lemma2.2>> search.
  Proof Completed!
  
  >> Theorem Lemma3:
      forall  L1 L2 L3 D1 D2,
        {D1 : rev_acc L1 L2 L3} =>
          {D2 : islist L2} => exists  D3, {D3 : islist L3}.
  
  Subgoal Lemma3:
  
  
  ==================================
  forall L1, forall L2, forall L3, forall D1, forall D2,
    {D1 : rev_acc L1 L2 L3} => {D2 : islist L2} => exists D3, {D3 : islist L3}
  
  Lemma3>> induction on 1.
  
  Subgoal Lemma3:
  
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  
  ==================================
  forall L1, forall L2, forall L3, forall D1, forall D2,
    {D1 : rev_acc L1 L2 L3}@ => {D2 : islist L2} => exists D3, {D3 : islist L3}
  
  Lemma3>> intros.
  
  Subgoal Lemma3:
  
  Vars: D2:o, D1:o, L3:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H1:{D1 : rev_acc L1 L2 L3}@
  H2:{D2 : islist L2}
  
  ==================================
  exists D3, {D3 : islist L3}
  
  Lemma3>> cases H1.
  
  Subgoal Lemma3.1:
  
  Vars: D:o, N:o, L4:o, D2:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H2:{D2 : islist L2}
  H3:{L4 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L4 (cons N L2) L3}*
  
  ==================================
  exists D3, {D3 : islist L3}
  
  Subgoal Lemma3.2 is:
   exists D3, {D3 : islist L3}
  
  Lemma3.1>> assert exists  D1, {D1 : islist cons N L2}.
  
  Subgoal Lemma3.1:
  
  Vars: D:o, N:o, L4:o, D2:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H2:{D2 : islist L2}
  H3:{L4 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L4 (cons N L2) L3}*
  
  ==================================
  exists D1, {D1 : islist (cons N L2)}
  
  Subgoal Lemma3.1 is:
   exists D3, {D3 : islist L3}
  
  Subgoal Lemma3.2 is:
   exists D3, {D3 : islist L3}
  
  Lemma3.1>> exists islist_cons N L2 D2.
  
  Subgoal Lemma3.1:
  
  Vars: D:o, N:o, L4:o, D2:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H2:{D2 : islist L2}
  H3:{L4 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L4 (cons N L2) L3}*
  
  ==================================
  {islist_cons N L2 D2 : islist (cons N L2)}
  
  Subgoal Lemma3.1 is:
   exists D3, {D3 : islist L3}
  
  Subgoal Lemma3.2 is:
   exists D3, {D3 : islist L3}
  
  Lemma3.1>> search.
  
  Subgoal Lemma3.1:
  
  Vars: D:o, N:o, L4:o, D2:o, D1:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H2:{D2 : islist L2}
  H3:{L4 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L4 (cons N L2) L3}*
  H8:{D1 : islist (cons N L2)}
  
  ==================================
  exists D3, {D3 : islist L3}
  
  Subgoal Lemma3.2 is:
   exists D3, {D3 : islist L3}
  
  Lemma3.1>> apply IH to H7 H8 with L1 = L4, L2 = cons N L2, L3 = L3, D1 = D, D2 = D1.
  
  Subgoal Lemma3.1:
  
  Vars: D3:o, D:o, N:o, L4:o, D2:o, D1:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H2:{D2 : islist L2}
  H3:{L4 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L4 (cons N L2) L3}*
  H8:{D1 : islist (cons N L2)}
  H9:{D3 : islist L3}
  
  ==================================
  exists D3, {D3 : islist L3}
  
  Subgoal Lemma3.2 is:
   exists D3, {D3 : islist L3}
  
  Lemma3.1>> exists D3.
  
  Subgoal Lemma3.1:
  
  Vars: D3:o, D:o, N:o, L4:o, D2:o, D1:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H2:{D2 : islist L2}
  H3:{L4 : list}*
  H4:{L2 : list}*
  H5:{L3 : list}*
  H6:{N : nat}*
  H7:{D : rev_acc L4 (cons N L2) L3}*
  H8:{D1 : islist (cons N L2)}
  H9:{D3 : islist L3}
  
  ==================================
  {D3 : islist L3}
  
  Subgoal Lemma3.2 is:
   exists D3, {D3 : islist L3}
  
  Lemma3.1>> search.
  
  Subgoal Lemma3.2:
  
  Vars: D2:o, L3:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H2:{D2 : islist L3}
  H3:{L3 : list}*
  
  ==================================
  exists D3, {D3 : islist L3}
  
  Lemma3.2>> exists D2.
  
  Subgoal Lemma3.2:
  
  Vars: D2:o, L3:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : islist L2} => exists D3, {D3 : islist L3}
  H2:{D2 : islist L3}
  H3:{L3 : list}*
  
  ==================================
  {D2 : islist L3}
  
  Lemma3.2>> search.
  Proof Completed!
  
  >> Theorem Lemma4:
      forall  L1 L2 D1,
        {D1 : islist L1} =>
          {L2 : list} => exists  L3 D2, {D2 : rev_acc L1 L2 L3}.
  
  Subgoal Lemma4:
  
  
  ==================================
  forall L1, forall L2, forall D1,
    {D1 : islist L1} =>
        {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  
  Lemma4>> induction on 1.
  
  Subgoal Lemma4:
  
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  
  ==================================
  forall L1, forall L2, forall D1,
    {D1 : islist L1}@ =>
        {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  
  Lemma4>> intros.
  
  Subgoal Lemma4:
  
  Vars: D1:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H1:{D1 : islist L1}@
  H2:{L2 : list}
  
  ==================================
  exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  
  Lemma4>> cases H1.
  
  Subgoal Lemma4.1:
  
  Vars: D:o, X:o, L:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{X : nat}*
  H4:{L : list}*
  H5:{D : islist L}*
  
  ==================================
  exists L3, exists D2, {D2 : rev_acc (cons X L) L2 L3}
  
  Subgoal Lemma4.2 is:
   exists L3, exists D2, {D2 : rev_acc nil L2 L3}
  
  Lemma4.1>> assert {cons X L2 : list}.
  
  Subgoal Lemma4.1:
  
  Vars: D:o, X:o, L:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{X : nat}*
  H4:{L : list}*
  H5:{D : islist L}*
  H6:{cons X L2 : list}
  
  ==================================
  exists L3, exists D2, {D2 : rev_acc (cons X L) L2 L3}
  
  Subgoal Lemma4.2 is:
   exists L3, exists D2, {D2 : rev_acc nil L2 L3}
  
  Lemma4.1>> apply IH to H5 H6 with L1 = L, L2 = cons X L2, D1 = D.
  
  Subgoal Lemma4.1:
  
  Vars: D2:o, L3:o, D:o, X:o, L:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{X : nat}*
  H4:{L : list}*
  H5:{D : islist L}*
  H6:{cons X L2 : list}
  H7:{D2 : rev_acc L (cons X L2) L3}
  
  ==================================
  exists L3, exists D2, {D2 : rev_acc (cons X L) L2 L3}
  
  Subgoal Lemma4.2 is:
   exists L3, exists D2, {D2 : rev_acc nil L2 L3}
  
  Lemma4.1>> assert {L3 : list}.
  
  Subgoal Lemma4.1:
  
  Vars: D2:o, L3:o, D:o, X:o, L:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{X : nat}*
  H4:{L : list}*
  H5:{D : islist L}*
  H6:{cons X L2 : list}
  H7:{D2 : rev_acc L (cons X L2) L3}
  H8:{L3 : list}
  
  ==================================
  exists L3, exists D2, {D2 : rev_acc (cons X L) L2 L3}
  
  Subgoal Lemma4.2 is:
   exists L3, exists D2, {D2 : rev_acc nil L2 L3}
  
  Lemma4.1>> exists L3.
  
  Subgoal Lemma4.1:
  
  Vars: D2:o, L3:o, D:o, X:o, L:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{X : nat}*
  H4:{L : list}*
  H5:{D : islist L}*
  H6:{cons X L2 : list}
  H7:{D2 : rev_acc L (cons X L2) L3}
  H8:{L3 : list}
  
  ==================================
  exists D2, {D2 : rev_acc (cons X L) L2 L3}
  
  Subgoal Lemma4.2 is:
   exists L3, exists D2, {D2 : rev_acc nil L2 L3}
  
  Lemma4.1>> exists rev_acc_cons L L2 L3 X D2.
  
  Subgoal Lemma4.1:
  
  Vars: D2:o, L3:o, D:o, X:o, L:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{X : nat}*
  H4:{L : list}*
  H5:{D : islist L}*
  H6:{cons X L2 : list}
  H7:{D2 : rev_acc L (cons X L2) L3}
  H8:{L3 : list}
  
  ==================================
  {rev_acc_cons L L2 L3 X D2 : rev_acc (cons X L) L2 L3}
  
  Subgoal Lemma4.2 is:
   exists L3, exists D2, {D2 : rev_acc nil L2 L3}
  
  Lemma4.1>> search.
  
  Subgoal Lemma4.2:
  
  Vars: L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  
  ==================================
  exists L3, exists D2, {D2 : rev_acc nil L2 L3}
  
  Lemma4.2>> exists L2.
  
  Subgoal Lemma4.2:
  
  Vars: L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  
  ==================================
  exists D2, {D2 : rev_acc nil L2 L2}
  
  Lemma4.2>> exists rev_acc_nil L2.
  
  Subgoal Lemma4.2:
  
  Vars: L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : islist L1}* =>
            {L2 : list} => exists L3, exists D2, {D2 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  
  ==================================
  {rev_acc_nil L2 : rev_acc nil L2 L2}
  
  Lemma4.2>> search.
  Proof Completed!
  
  >> Theorem rev_rev:
      forall  L1 L2 D1, {D1 : rev L1 L2} => exists  D2, {D2 : rev L2 L1}.
  
  Subgoal rev_rev:
  
  
  ==================================
  forall L1, forall L2, forall D1,
    {D1 : rev L1 L2} => exists D2, {D2 : rev L2 L1}
  
  rev_rev>> intros.
  
  Subgoal rev_rev:
  
  Vars: D1:o, L2:o, L1:o
  H1:{D1 : rev L1 L2}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> cases H1.
  
  Subgoal rev_rev:
  
  Vars: D:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> assert exists  D1, {D1 : islist nil}.
  
  Subgoal rev_rev:
  
  Vars: D:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  
  ==================================
  exists D1, {D1 : islist nil}
  
  Subgoal rev_rev is:
   exists D2, {D2 : rev L2 L1}
  
  rev_rev>> exists islist_nil.
  
  Subgoal rev_rev:
  
  Vars: D:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  
  ==================================
  {islist_nil : islist nil}
  
  Subgoal rev_rev is:
   exists D2, {D2 : rev L2 L1}
  
  rev_rev>> search.
  
  Subgoal rev_rev:
  
  Vars: D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> apply Lemma3 to H4 H5 with L1 = L1, L2 = nil, L3 = L2, D1 = D, D2 = D1.
  
  Subgoal rev_rev:
  
  Vars: D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> assert {nil : list}.
  
  Subgoal rev_rev:
  
  Vars: D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  H7:{nil : list}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> apply Lemma4 to H6 H7 with L1 = L2, L2 = nil, D1 = D3.
  
  Subgoal rev_rev:
  
  Vars: D2:o, L3:o, D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  H7:{nil : list}
  H8:{D2 : rev_acc L2 nil L3}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> assert exists  D4, {D4 : rev_acc nil L1 L1}.
  
  Subgoal rev_rev:
  
  Vars: D2:o, L3:o, D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  H7:{nil : list}
  H8:{D2 : rev_acc L2 nil L3}
  
  ==================================
  exists D4, {D4 : rev_acc nil L1 L1}
  
  Subgoal rev_rev is:
   exists D2, {D2 : rev L2 L1}
  
  rev_rev>> exists rev_acc_nil L1.
  
  Subgoal rev_rev:
  
  Vars: D2:o, L3:o, D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  H7:{nil : list}
  H8:{D2 : rev_acc L2 nil L3}
  
  ==================================
  {rev_acc_nil L1 : rev_acc nil L1 L1}
  
  Subgoal rev_rev is:
   exists D2, {D2 : rev L2 L1}
  
  rev_rev>> search.
  
  Subgoal rev_rev:
  
  Vars: D4:o, D2:o, L3:o, D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  H7:{nil : list}
  H8:{D2 : rev_acc L2 nil L3}
  H9:{D4 : rev_acc nil L1 L1}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> apply Lemma2 to H4 H8 H9 with a = L1, B = nil, AB = L2, ba = L3, ba2 = L1, D1
      = D, D2 = D2, D3 = D4.
  
  Subgoal rev_rev:
  
  Vars: D5:o, D4:o, D2:o, L3:o, D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  H7:{nil : list}
  H8:{D2 : rev_acc L2 nil L3}
  H9:{D4 : rev_acc nil L1 L1}
  H10:{D5 : eq_list L3 L1}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> cases H10.
  
  Subgoal rev_rev:
  
  Vars: D4:o, D2:o, D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  H7:{nil : list}
  H8:{D2 : rev_acc L2 nil L1}
  H9:{D4 : rev_acc nil L1 L1}
  H11:{L1 : list}
  
  ==================================
  exists D2, {D2 : rev L2 L1}
  
  rev_rev>> exists rev_nil_acc L2 L1 D2.
  
  Subgoal rev_rev:
  
  Vars: D4:o, D2:o, D3:o, D:o, D1:o, L2:o, L1:o
  H2:{L1 : list}
  H3:{L2 : list}
  H4:{D : rev_acc L1 nil L2}
  H5:{D1 : islist nil}
  H6:{D3 : islist L2}
  H7:{nil : list}
  H8:{D2 : rev_acc L2 nil L1}
  H9:{D4 : rev_acc nil L1 L1}
  H11:{L1 : list}
  
  ==================================
  {rev_nil_acc L2 L1 D2 : rev L2 L1}
  
  rev_rev>> search.
  Proof Completed!
  
  >> Goodbye!
