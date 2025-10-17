  $ adelfa -i lists.ath
  Welcome!
  >> Specification "lists.lf".
  
  >> Theorem app_assoc:
      forall  L1 L2 L3 L23 L4 D1 D2,
        {D1 : append L2 L3 L23} =>
          {D2 : append L1 L23 L4} =>
            exists  L12 D3 D4,
              {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}.
  
  Subgoal app_assoc:
  
  
  ==================================
  forall L1, forall L2, forall L3, forall L23, forall L4, forall D1, forall D2,
    {D1 : append L2 L3 L23} =>
        {D2 : append L1 L23 L4} =>
            exists L12, exists D3, exists D4,
              {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc>> induction on 2.
  
  Subgoal app_assoc:
  
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  
  ==================================
  forall L1, forall L2, forall L3, forall L23, forall L4, forall D1, forall D2,
    {D1 : append L2 L3 L23} =>
        {D2 : append L1 L23 L4}@ =>
            exists L12, exists D3, exists D4,
              {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc>> intros.
  
  Subgoal app_assoc:
  
  Vars: D2:o, D1:o, L4:o, L23:o, L3:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H2:{D2 : append L1 L23 L4}@
  
  ==================================
  exists L12, exists D3, exists D4,
    {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc>> cases H2.
  
  Subgoal app_assoc.1:
  
  Vars: D:o, L5:o, N:o, L7:o, D1:o, L23:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H3:{L5 : list}*
  H4:{L23 : list}*
  H5:{L7 : list}*
  H6:{N : nat}*
  H7:{D : append L5 L23 L7}*
  
  ==================================
  exists L12, exists D3, exists D4,
    {D3 : append (cons N L5) L2 L12} /\ {D4 : append L12 L3 (cons N L7)}
  
  Subgoal app_assoc.2 is:
   exists L12, exists D3, exists D4,
     {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.1>> apply IH to H1 H7.
  
  Subgoal app_assoc.1:
  
  Vars: D4:o, D3:o, L12:o, D:o, L5:o, N:o, L7:o, D1:o, L23:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H3:{L5 : list}*
  H4:{L23 : list}*
  H5:{L7 : list}*
  H6:{N : nat}*
  H7:{D : append L5 L23 L7}*
  H8:{D3 : append L5 L2 L12} /\ {D4 : append L12 L3 L7}
  
  ==================================
  exists L12, exists D3, exists D4,
    {D3 : append (cons N L5) L2 L12} /\ {D4 : append L12 L3 (cons N L7)}
  
  Subgoal app_assoc.2 is:
   exists L12, exists D3, exists D4,
     {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.1>> cases H8.
  
  Subgoal app_assoc.1:
  
  Vars: D4:o, D3:o, L12:o, D:o, L5:o, N:o, L7:o, D1:o, L23:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H3:{L5 : list}*
  H4:{L23 : list}*
  H5:{L7 : list}*
  H6:{N : nat}*
  H7:{D : append L5 L23 L7}*
  H9:{D3 : append L5 L2 L12}
  H10:{D4 : append L12 L3 L7}
  
  ==================================
  exists L12, exists D3, exists D4,
    {D3 : append (cons N L5) L2 L12} /\ {D4 : append L12 L3 (cons N L7)}
  
  Subgoal app_assoc.2 is:
   exists L12, exists D3, exists D4,
     {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.1>> exists cons N L12.
  
  Subgoal app_assoc.1:
  
  Vars: D4:o, D3:o, L12:o, D:o, L5:o, N:o, L7:o, D1:o, L23:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H3:{L5 : list}*
  H4:{L23 : list}*
  H5:{L7 : list}*
  H6:{N : nat}*
  H7:{D : append L5 L23 L7}*
  H9:{D3 : append L5 L2 L12}
  H10:{D4 : append L12 L3 L7}
  
  ==================================
  exists D3, exists D4,
    {D3 : append (cons N L5) L2 (cons N L12)} /\
        {D4 : append (cons N L12) L3 (cons N L7)}
  
  Subgoal app_assoc.2 is:
   exists L12, exists D3, exists D4,
     {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.1>> exists append_cons L5 L2 L12 N D3.
  
  Subgoal app_assoc.1:
  
  Vars: D4:o, D3:o, L12:o, D:o, L5:o, N:o, L7:o, D1:o, L23:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H3:{L5 : list}*
  H4:{L23 : list}*
  H5:{L7 : list}*
  H6:{N : nat}*
  H7:{D : append L5 L23 L7}*
  H9:{D3 : append L5 L2 L12}
  H10:{D4 : append L12 L3 L7}
  
  ==================================
  exists D4,
    {append_cons L5 L2 L12 N D3 : append (cons N L5) L2 (cons N L12)} /\
        {D4 : append (cons N L12) L3 (cons N L7)}
  
  Subgoal app_assoc.2 is:
   exists L12, exists D3, exists D4,
     {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.1>> exists append_cons L12 L3 L7 N D4.
  
  Subgoal app_assoc.1:
  
  Vars: D4:o, D3:o, L12:o, D:o, L5:o, N:o, L7:o, D1:o, L23:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H3:{L5 : list}*
  H4:{L23 : list}*
  H5:{L7 : list}*
  H6:{N : nat}*
  H7:{D : append L5 L23 L7}*
  H9:{D3 : append L5 L2 L12}
  H10:{D4 : append L12 L3 L7}
  
  ==================================
  {append_cons L5 L2 L12 N D3 : append (cons N L5) L2 (cons N L12)} /\
      {append_cons L12 L3 L7 N D4 : append (cons N L12) L3 (cons N L7)}
  
  Subgoal app_assoc.2 is:
   exists L12, exists D3, exists D4,
     {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.1>> split.
  
  Subgoal app_assoc.1:
  
  Vars: D4:o, D3:o, L12:o, D:o, L5:o, N:o, L7:o, D1:o, L23:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H3:{L5 : list}*
  H4:{L23 : list}*
  H5:{L7 : list}*
  H6:{N : nat}*
  H7:{D : append L5 L23 L7}*
  H9:{D3 : append L5 L2 L12}
  H10:{D4 : append L12 L3 L7}
  
  ==================================
  {append_cons L5 L2 L12 N D3 : append (cons N L5) L2 (cons N L12)}
  
  Subgoal app_assoc.1 is:
   {append_cons L12 L3 L7 N D4 : append (cons N L12) L3 (cons N L7)}
  
  Subgoal app_assoc.2 is:
   exists L12, exists D3, exists D4,
     {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.1>> search.
  
  Subgoal app_assoc.1:
  
  Vars: D4:o, D3:o, L12:o, D:o, L5:o, N:o, L7:o, D1:o, L23:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L23}
  H3:{L5 : list}*
  H4:{L23 : list}*
  H5:{L7 : list}*
  H6:{N : nat}*
  H7:{D : append L5 L23 L7}*
  H9:{D3 : append L5 L2 L12}
  H10:{D4 : append L12 L3 L7}
  
  ==================================
  {append_cons L12 L3 L7 N D4 : append (cons N L12) L3 (cons N L7)}
  
  Subgoal app_assoc.2 is:
   exists L12, exists D3, exists D4,
     {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.1>> search.
  
  Subgoal app_assoc.2:
  
  Vars: D1:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L4}
  H3:{L4 : list}*
  
  ==================================
  exists L12, exists D3, exists D4,
    {D3 : append nil L2 L12} /\ {D4 : append L12 L3 L4}
  
  app_assoc.2>> exists L2.
  
  Subgoal app_assoc.2:
  
  Vars: D1:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L4}
  H3:{L4 : list}*
  
  ==================================
  exists D3, exists D4, {D3 : append nil L2 L2} /\ {D4 : append L2 L3 L4}
  
  app_assoc.2>> exists append_nil L2.
  
  Subgoal app_assoc.2:
  
  Vars: D1:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L4}
  H3:{L4 : list}*
  
  ==================================
  exists D4, {append_nil L2 : append nil L2 L2} /\ {D4 : append L2 L3 L4}
  
  app_assoc.2>> exists D1.
  
  Subgoal app_assoc.2:
  
  Vars: D1:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L4}
  H3:{L4 : list}*
  
  ==================================
  {append_nil L2 : append nil L2 L2} /\ {D1 : append L2 L3 L4}
  
  app_assoc.2>> split.
  
  Subgoal app_assoc.2:
  
  Vars: D1:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L4}
  H3:{L4 : list}*
  
  ==================================
  {append_nil L2 : append nil L2 L2}
  
  Subgoal app_assoc.2 is:
   {D1 : append L2 L3 L4}
  
  app_assoc.2>> search.
  
  Subgoal app_assoc.2:
  
  Vars: D1:o, L4:o, L3:o, L2:o
  IH:
      forall L1, forall L2, forall L3, forall L23, forall L4, forall D1,
        forall D2,
        {D1 : append L2 L3 L23} =>
            {D2 : append L1 L23 L4}* =>
                exists L12, exists D3, exists D4,
                  {D3 : append L1 L2 L12} /\ {D4 : append L12 L3 L4}
  H1:{D1 : append L2 L3 L4}
  H3:{L4 : list}*
  
  ==================================
  {D1 : append L2 L3 L4}
  
  app_assoc.2>> search.
  Proof Completed!
  
  >> Theorem app_identity:
      forall  L1 L2 D,
        {D : append L1 nil L2} => exists  R, {R : eq_list L1 L2}.
  
  Subgoal app_identity:
  
  
  ==================================
  forall L1, forall L2, forall D,
    {D : append L1 nil L2} => exists R, {R : eq_list L1 L2}
  
  app_identity>> induction on 1.
  
  Subgoal app_identity:
  
  IH:
      forall L1, forall L2, forall D,
        {D : append L1 nil L2}* => exists R, {R : eq_list L1 L2}
  
  ==================================
  forall L1, forall L2, forall D,
    {D : append L1 nil L2}@ => exists R, {R : eq_list L1 L2}
  
  app_identity>> intros.
  
  Subgoal app_identity:
  
  Vars: D:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall D,
        {D : append L1 nil L2}* => exists R, {R : eq_list L1 L2}
  H1:{D : append L1 nil L2}@
  
  ==================================
  exists R, {R : eq_list L1 L2}
  
  app_identity>> cases H1.
  
  Subgoal app_identity.1:
  
  Vars: D1:o, L3:o, N:o, L5:o
  IH:
      forall L1, forall L2, forall D,
        {D : append L1 nil L2}* => exists R, {R : eq_list L1 L2}
  H2:{L3 : list}*
  H3:{nil : list}*
  H4:{L5 : list}*
  H5:{N : nat}*
  H6:{D1 : append L3 nil L5}*
  
  ==================================
  exists R, {R : eq_list (cons N L3) (cons N L5)}
  
  Subgoal app_identity.2 is:
   exists R, {R : eq_list nil nil}
  
  app_identity.1>> apply IH to H6.
  
  Subgoal app_identity.1:
  
  Vars: R:o, D1:o, L3:o, N:o, L5:o
  IH:
      forall L1, forall L2, forall D,
        {D : append L1 nil L2}* => exists R, {R : eq_list L1 L2}
  H2:{L3 : list}*
  H3:{nil : list}*
  H4:{L5 : list}*
  H5:{N : nat}*
  H6:{D1 : append L3 nil L5}*
  H7:{R : eq_list L3 L5}
  
  ==================================
  exists R, {R : eq_list (cons N L3) (cons N L5)}
  
  Subgoal app_identity.2 is:
   exists R, {R : eq_list nil nil}
  
  app_identity.1>> cases H7.
  
  Subgoal app_identity.1:
  
  Vars: D1:o, N:o, L5:o
  IH:
      forall L1, forall L2, forall D,
        {D : append L1 nil L2}* => exists R, {R : eq_list L1 L2}
  H2:{L5 : list}*
  H3:{nil : list}*
  H4:{L5 : list}*
  H5:{N : nat}*
  H6:{D1 : append L5 nil L5}*
  H8:{L5 : list}
  
  ==================================
  exists R, {R : eq_list (cons N L5) (cons N L5)}
  
  Subgoal app_identity.2 is:
   exists R, {R : eq_list nil nil}
  
  app_identity.1>> exists refl_list cons N L5.
  
  Subgoal app_identity.1:
  
  Vars: D1:o, N:o, L5:o
  IH:
      forall L1, forall L2, forall D,
        {D : append L1 nil L2}* => exists R, {R : eq_list L1 L2}
  H2:{L5 : list}*
  H3:{nil : list}*
  H4:{L5 : list}*
  H5:{N : nat}*
  H6:{D1 : append L5 nil L5}*
  H8:{L5 : list}
  
  ==================================
  {refl_list (cons N L5) : eq_list (cons N L5) (cons N L5)}
  
  Subgoal app_identity.2 is:
   exists R, {R : eq_list nil nil}
  
  app_identity.1>> search.
  
  Subgoal app_identity.2:
  
  IH:
      forall L1, forall L2, forall D,
        {D : append L1 nil L2}* => exists R, {R : eq_list L1 L2}
  H2:{nil : list}*
  
  ==================================
  exists R, {R : eq_list nil nil}
  
  app_identity.2>> exists refl_list nil.
  
  Subgoal app_identity.2:
  
  IH:
      forall L1, forall L2, forall D,
        {D : append L1 nil L2}* => exists R, {R : eq_list L1 L2}
  H2:{nil : list}*
  
  ==================================
  {refl_list nil : eq_list nil nil}
  
  app_identity.2>> search.
  Proof Completed!
  
  >> Theorem rev_app_swap:
      forall  A B a b AB ba D1 D2 D3 D4,
        {D1 : append A B AB} =>
          {D2 : rev_app A a} =>
            {D3 : rev_app B b} =>
              {D4 : append b a ba} => exists  D5, {D5 : rev_app AB ba}.
  
  Subgoal rev_app_swap:
  
  
  ==================================
  forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
    forall D2, forall D3, forall D4,
    {D1 : append A B AB} =>
        {D2 : rev_app A a} =>
            {D3 : rev_app B b} =>
                {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap>> induction on 1.
  
  Subgoal rev_app_swap:
  
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  
  ==================================
  forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
    forall D2, forall D3, forall D4,
    {D1 : append A B AB}@ =>
        {D2 : rev_app A a} =>
            {D3 : rev_app B b} =>
                {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap>> intros.
  
  Subgoal rev_app_swap:
  
  Vars: D4:o, D3:o, D2:o, D1:o, ba:o, AB:o, b:o, a:o, B:o, A:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H1:{D1 : append A B AB}@
  H2:{D2 : rev_app A a}
  H3:{D3 : rev_app B b}
  H4:{D4 : append b a ba}
  
  ==================================
  exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap>> cases H1.
  
  Subgoal rev_app_swap.1:
  
  Vars: D:o, L1:o, N:o, L3:o, D4:o, D3:o, D2:o, ba:o, b:o, a:o, B:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H2:{D2 : rev_app (cons N L1) a}
  H3:{D3 : rev_app B b}
  H4:{D4 : append b a ba}
  H5:{L1 : list}*
  H6:{B : list}*
  H7:{L3 : list}*
  H8:{N : nat}*
  H9:{D : append L1 B L3}*
  
  ==================================
  exists D5, {D5 : rev_app (cons N L3) ba}
  
  Subgoal rev_app_swap.2 is:
   exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.1>> cases H2.
  
  Subgoal rev_app_swap.1:
  
  Vars: B1:o, D5:o, D6:o, D:o, L1:o, N:o, L3:o, D4:o, D3:o, ba:o, b:o, a:o, B:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app B b}
  H4:{D4 : append b a ba}
  H5:{L1 : list}*
  H6:{B : list}*
  H7:{L3 : list}*
  H8:{N : nat}*
  H9:{D : append L1 B L3}*
  H10:{N : nat}
  H11:{L1 : list}
  H12:{B1 : list}
  H13:{a : list}
  H14:{D5 : rev_app L1 B1}
  H15:{D6 : append B1 (cons N nil) a}
  
  ==================================
  exists D5, {D5 : rev_app (cons N L3) ba}
  
  Subgoal rev_app_swap.2 is:
   exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.1>> apply app_assoc to H15 H4.
  
  Subgoal rev_app_swap.1:
  
  Vars: L12:o, B1:o, D5:o, D6:o, D:o, L1:o, N:o, L3:o, D4:o, D3:o, D2:o, D1:o,
          ba:o, b:o, a:o, B:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app B b}
  H4:{D4 : append b a ba}
  H5:{L1 : list}*
  H6:{B : list}*
  H7:{L3 : list}*
  H8:{N : nat}*
  H9:{D : append L1 B L3}*
  H10:{N : nat}
  H11:{L1 : list}
  H12:{B1 : list}
  H13:{a : list}
  H14:{D5 : rev_app L1 B1}
  H15:{D6 : append B1 (cons N nil) a}
  H16:{D1 : append b B1 L12} /\ {D2 : append L12 (cons N nil) ba}
  
  ==================================
  exists D5, {D5 : rev_app (cons N L3) ba}
  
  Subgoal rev_app_swap.2 is:
   exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.1>> cases H16.
  
  Subgoal rev_app_swap.1:
  
  Vars: L12:o, B1:o, D5:o, D6:o, D:o, L1:o, N:o, L3:o, D4:o, D3:o, D2:o, D1:o,
          ba:o, b:o, a:o, B:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app B b}
  H4:{D4 : append b a ba}
  H5:{L1 : list}*
  H6:{B : list}*
  H7:{L3 : list}*
  H8:{N : nat}*
  H9:{D : append L1 B L3}*
  H10:{N : nat}
  H11:{L1 : list}
  H12:{B1 : list}
  H13:{a : list}
  H14:{D5 : rev_app L1 B1}
  H15:{D6 : append B1 (cons N nil) a}
  H17:{D1 : append b B1 L12}
  H18:{D2 : append L12 (cons N nil) ba}
  
  ==================================
  exists D5, {D5 : rev_app (cons N L3) ba}
  
  Subgoal rev_app_swap.2 is:
   exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.1>> apply IH to H9 H14 H3 H17.
  
  Subgoal rev_app_swap.1:
  
  Vars: D7:o, L12:o, B1:o, D5:o, D6:o, D:o, L1:o, N:o, L3:o, D4:o, D3:o, D2:o,
          D1:o, ba:o, b:o, a:o, B:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app B b}
  H4:{D4 : append b a ba}
  H5:{L1 : list}*
  H6:{B : list}*
  H7:{L3 : list}*
  H8:{N : nat}*
  H9:{D : append L1 B L3}*
  H10:{N : nat}
  H11:{L1 : list}
  H12:{B1 : list}
  H13:{a : list}
  H14:{D5 : rev_app L1 B1}
  H15:{D6 : append B1 (cons N nil) a}
  H17:{D1 : append b B1 L12}
  H18:{D2 : append L12 (cons N nil) ba}
  H19:{D7 : rev_app L3 L12}
  
  ==================================
  exists D5, {D5 : rev_app (cons N L3) ba}
  
  Subgoal rev_app_swap.2 is:
   exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.1>> exists rev_app_cons N L3 L12 ba D7 D2.
  
  Subgoal rev_app_swap.1:
  
  Vars: D7:o, L12:o, B1:o, D5:o, D6:o, D:o, L1:o, N:o, L3:o, D4:o, D3:o, D2:o,
          D1:o, ba:o, b:o, a:o, B:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app B b}
  H4:{D4 : append b a ba}
  H5:{L1 : list}*
  H6:{B : list}*
  H7:{L3 : list}*
  H8:{N : nat}*
  H9:{D : append L1 B L3}*
  H10:{N : nat}
  H11:{L1 : list}
  H12:{B1 : list}
  H13:{a : list}
  H14:{D5 : rev_app L1 B1}
  H15:{D6 : append B1 (cons N nil) a}
  H17:{D1 : append b B1 L12}
  H18:{D2 : append L12 (cons N nil) ba}
  H19:{D7 : rev_app L3 L12}
  
  ==================================
  {rev_app_cons N L3 L12 ba D7 D2 : rev_app (cons N L3) ba}
  
  Subgoal rev_app_swap.2 is:
   exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.1>> search.
  
  Subgoal rev_app_swap.2:
  
  Vars: D4:o, D3:o, D2:o, ba:o, AB:o, b:o, a:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H2:{D2 : rev_app nil a}
  H3:{D3 : rev_app AB b}
  H4:{D4 : append b a ba}
  H5:{AB : list}*
  
  ==================================
  exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.2>> cases H2.
  
  Subgoal rev_app_swap.2:
  
  Vars: D4:o, D3:o, ba:o, AB:o, b:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app AB b}
  H4:{D4 : append b nil ba}
  H5:{AB : list}*
  
  ==================================
  exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.2>> apply app_identity to H4.
  
  Subgoal rev_app_swap.2:
  
  Vars: R:o, D4:o, D3:o, ba:o, AB:o, b:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app AB b}
  H4:{D4 : append b nil ba}
  H5:{AB : list}*
  H6:{R : eq_list b ba}
  
  ==================================
  exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.2>> cases H6.
  
  Subgoal rev_app_swap.2:
  
  Vars: D4:o, D3:o, ba:o, AB:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app AB ba}
  H4:{D4 : append ba nil ba}
  H5:{AB : list}*
  H7:{ba : list}
  
  ==================================
  exists D5, {D5 : rev_app AB ba}
  
  rev_app_swap.2>> exists D3.
  
  Subgoal rev_app_swap.2:
  
  Vars: D4:o, D3:o, ba:o, AB:o
  IH:
      forall A, forall B, forall a, forall b, forall AB, forall ba, forall D1,
        forall D2, forall D3, forall D4,
        {D1 : append A B AB}* =>
            {D2 : rev_app A a} =>
                {D3 : rev_app B b} =>
                    {D4 : append b a ba} => exists D5, {D5 : rev_app AB ba}
  H3:{D3 : rev_app AB ba}
  H4:{D4 : append ba nil ba}
  H5:{AB : list}*
  H7:{ba : list}
  
  ==================================
  {D3 : rev_app AB ba}
  
  rev_app_swap.2>> search.
  Proof Completed!
  
  >> Theorem rev_app_rev:
      forall  L1 L2 D1,
        {D1 : rev_app L1 L2} => exists  D2, {D2 : rev_app L2 L1}.
  
  Subgoal rev_app_rev:
  
  
  ==================================
  forall L1, forall L2, forall D1,
    {D1 : rev_app L1 L2} => exists D2, {D2 : rev_app L2 L1}
  
  rev_app_rev>> induction on 1.
  
  Subgoal rev_app_rev:
  
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  
  ==================================
  forall L1, forall L2, forall D1,
    {D1 : rev_app L1 L2}@ => exists D2, {D2 : rev_app L2 L1}
  
  rev_app_rev>> intros.
  
  Subgoal rev_app_rev:
  
  Vars: D1:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H1:{D1 : rev_app L1 L2}@
  
  ==================================
  exists D2, {D2 : rev_app L2 L1}
  
  rev_app_rev>> cases H1.
  
  Subgoal rev_app_rev.1:
  
  Vars: B:o, D:o, D2:o, N:o, A:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  
  ==================================
  exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> apply IH to H6.
  
  Subgoal rev_app_rev.1:
  
  Vars: B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  
  ==================================
  exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> assert exists  D3, {D3 : rev_app cons N nil cons N nil}.
  
  Subgoal rev_app_rev.1:
  
  Vars: B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  
  ==================================
  exists D3, {D3 : rev_app (cons N nil) (cons N nil)}
  
  Subgoal rev_app_rev.1 is:
   exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> exists rev_app_cons N nil nil cons N nil rev_app_nil append_nil cons N nil.
  
  Subgoal rev_app_rev.1:
  
  Vars: B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  
  ==================================
  {rev_app_cons N nil nil (cons N nil) rev_app_nil (append_nil (cons N nil)) :
    rev_app (cons N nil) (cons N nil)}
  
  Subgoal rev_app_rev.1 is:
   exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> search.
  
  Subgoal rev_app_rev.1:
  
  Vars: D3:o, B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  H9:{D3 : rev_app (cons N nil) (cons N nil)}
  
  ==================================
  exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> assert exists  D4, {D4 : append cons N nil A cons N A}.
  
  Subgoal rev_app_rev.1:
  
  Vars: D3:o, B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  H9:{D3 : rev_app (cons N nil) (cons N nil)}
  
  ==================================
  exists D4, {D4 : append (cons N nil) A (cons N A)}
  
  Subgoal rev_app_rev.1 is:
   exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> exists append_cons nil A A N append_nil A.
  
  Subgoal rev_app_rev.1:
  
  Vars: D3:o, B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  H9:{D3 : rev_app (cons N nil) (cons N nil)}
  
  ==================================
  {append_cons nil A A N (append_nil A) : append (cons N nil) A (cons N A)}
  
  Subgoal rev_app_rev.1 is:
   exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> search.
  
  Subgoal rev_app_rev.1:
  
  Vars: D4:o, D3:o, B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  H9:{D3 : rev_app (cons N nil) (cons N nil)}
  H10:{D4 : append (cons N nil) A (cons N A)}
  
  ==================================
  exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> apply rev_app_swap to H7 H8 H9 H10.
  
  Subgoal rev_app_rev.1:
  
  Vars: D5:o, D4:o, D3:o, B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  H9:{D3 : rev_app (cons N nil) (cons N nil)}
  H10:{D4 : append (cons N nil) A (cons N A)}
  H11:{D5 : rev_app L2 (cons N A)}
  
  ==================================
  exists D2, {D2 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> exists D5.
  
  Subgoal rev_app_rev.1:
  
  Vars: D5:o, D4:o, D3:o, B:o, D:o, D2:o, N:o, A:o, D1:o, L2:o
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  H2:{N : nat}*
  H3:{A : list}*
  H4:{B : list}*
  H5:{L2 : list}*
  H6:{D : rev_app A B}*
  H7:{D2 : append B (cons N nil) L2}*
  H8:{D1 : rev_app B A}
  H9:{D3 : rev_app (cons N nil) (cons N nil)}
  H10:{D4 : append (cons N nil) A (cons N A)}
  H11:{D5 : rev_app L2 (cons N A)}
  
  ==================================
  {D5 : rev_app L2 (cons N A)}
  
  Subgoal rev_app_rev.2 is:
   exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.1>> search.
  
  Subgoal rev_app_rev.2:
  
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  
  ==================================
  exists D2, {D2 : rev_app nil nil}
  
  rev_app_rev.2>> exists rev_app_nil.
  
  Subgoal rev_app_rev.2:
  
  IH:
      forall L1, forall L2, forall D1,
        {D1 : rev_app L1 L2}* => exists D2, {D2 : rev_app L2 L1}
  
  ==================================
  {rev_app_nil : rev_app nil nil}
  
  rev_app_rev.2>> search.
  Proof Completed!
  
  >> Theorem rev_acc_func:
      forall  L1 L2 L3 L4 D1 D2,
        {D1 : rev_acc L1 L2 L3} =>
          {D2 : rev_acc L1 L2 L4} => exists  D3, {D3 : eq_list L3 L4}.
  
  Subgoal rev_acc_func:
  
  
  ==================================
  forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
    {D1 : rev_acc L1 L2 L3} =>
        {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  
  rev_acc_func>> induction on 1.
  
  Subgoal rev_acc_func:
  
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  
  ==================================
  forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
    {D1 : rev_acc L1 L2 L3}@ =>
        {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  
  rev_acc_func>> intros.
  
  Subgoal rev_acc_func:
  
  Vars: D2:o, D1:o, L4:o, L3:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H1:{D1 : rev_acc L1 L2 L3}@
  H2:{D2 : rev_acc L1 L2 L4}
  
  ==================================
  exists D3, {D3 : eq_list L3 L4}
  
  rev_acc_func>> cases H1.
  
  Subgoal rev_acc_func.1:
  
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
  
  Subgoal rev_acc_func.2 is:
   exists D3, {D3 : eq_list L3 L4}
  
  rev_acc_func.1>> cases H2.
  
  Subgoal rev_acc_func.1:
  
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
  
  Subgoal rev_acc_func.2 is:
   exists D3, {D3 : eq_list L3 L4}
  
  rev_acc_func.1>> apply IH to H7 H12.
  
  Subgoal rev_acc_func.1:
  
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
  
  Subgoal rev_acc_func.2 is:
   exists D3, {D3 : eq_list L3 L4}
  
  rev_acc_func.1>> exists D1.
  
  Subgoal rev_acc_func.1:
  
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
  
  Subgoal rev_acc_func.2 is:
   exists D3, {D3 : eq_list L3 L4}
  
  rev_acc_func.1>> search.
  
  Subgoal rev_acc_func.2:
  
  Vars: D2:o, L4:o, L3:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H2:{D2 : rev_acc nil L3 L4}
  H3:{L3 : list}*
  
  ==================================
  exists D3, {D3 : eq_list L3 L4}
  
  rev_acc_func.2>> cases H2.
  
  Subgoal rev_acc_func.2:
  
  Vars: L4:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H3:{L4 : list}*
  H4:{L4 : list}
  
  ==================================
  exists D3, {D3 : eq_list L4 L4}
  
  rev_acc_func.2>> exists refl_list L4.
  
  Subgoal rev_acc_func.2:
  
  Vars: L4:o
  IH:
      forall L1, forall L2, forall L3, forall L4, forall D1, forall D2,
        {D1 : rev_acc L1 L2 L3}* =>
            {D2 : rev_acc L1 L2 L4} => exists D3, {D3 : eq_list L3 L4}
  H3:{L4 : list}*
  H4:{L4 : list}
  
  ==================================
  {refl_list L4 : eq_list L4 L4}
  
  rev_acc_func.2>> search.
  Proof Completed!
  
  >> Theorem rev_acc_exists:
      forall  L1 L2,
        {L1 : list} => {L2 : list} => exists  L3 D1, {D1 : rev_acc L1 L2 L3}.
  
  Subgoal rev_acc_exists:
  
  
  ==================================
  forall L1, forall L2,
    {L1 : list} => {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  
  rev_acc_exists>> induction on 1.
  
  Subgoal rev_acc_exists:
  
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  
  ==================================
  forall L1, forall L2,
    {L1 : list}@ =>
        {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  
  rev_acc_exists>> intros.
  
  Subgoal rev_acc_exists:
  
  Vars: L2:o, L1:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H1:{L1 : list}@
  H2:{L2 : list}
  
  ==================================
  exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  
  rev_acc_exists>> cases H1.
  
  Subgoal rev_acc_exists.1:
  
  Vars: n:o, l:o, L2:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{n : nat}*
  H4:{l : list}*
  
  ==================================
  exists L3, exists D1, {D1 : rev_acc (cons n l) L2 L3}
  
  Subgoal rev_acc_exists.2 is:
   exists L3, exists D1, {D1 : rev_acc nil L2 L3}
  
  rev_acc_exists.1>> assert {cons n L2 : list}.
  
  Subgoal rev_acc_exists.1:
  
  Vars: n:o, l:o, L2:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{n : nat}*
  H4:{l : list}*
  H5:{cons n L2 : list}
  
  ==================================
  exists L3, exists D1, {D1 : rev_acc (cons n l) L2 L3}
  
  Subgoal rev_acc_exists.2 is:
   exists L3, exists D1, {D1 : rev_acc nil L2 L3}
  
  rev_acc_exists.1>> apply IH to H4 H5.
  
  Subgoal rev_acc_exists.1:
  
  Vars: D1:o, L3:o, n:o, l:o, L2:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{n : nat}*
  H4:{l : list}*
  H5:{cons n L2 : list}
  H6:{D1 : rev_acc l (cons n L2) L3}
  
  ==================================
  exists L3, exists D1, {D1 : rev_acc (cons n l) L2 L3}
  
  Subgoal rev_acc_exists.2 is:
   exists L3, exists D1, {D1 : rev_acc nil L2 L3}
  
  rev_acc_exists.1>> exists L3.
  
  Subgoal rev_acc_exists.1:
  
  Vars: D1:o, L3:o, n:o, l:o, L2:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{n : nat}*
  H4:{l : list}*
  H5:{cons n L2 : list}
  H6:{D1 : rev_acc l (cons n L2) L3}
  
  ==================================
  exists D1, {D1 : rev_acc (cons n l) L2 L3}
  
  Subgoal rev_acc_exists.2 is:
   exists L3, exists D1, {D1 : rev_acc nil L2 L3}
  
  rev_acc_exists.1>> exists rev_acc_cons l L2 L3 n D1.
  
  Subgoal rev_acc_exists.1:
  
  Vars: D1:o, L3:o, n:o, l:o, L2:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  H3:{n : nat}*
  H4:{l : list}*
  H5:{cons n L2 : list}
  H6:{D1 : rev_acc l (cons n L2) L3}
  
  ==================================
  {rev_acc_cons l L2 L3 n D1 : rev_acc (cons n l) L2 L3}
  
  Subgoal rev_acc_exists.2 is:
   exists L3, exists D1, {D1 : rev_acc nil L2 L3}
  
  rev_acc_exists.1>> search.
  
  Subgoal rev_acc_exists.2:
  
  Vars: L2:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  
  ==================================
  exists L3, exists D1, {D1 : rev_acc nil L2 L3}
  
  rev_acc_exists.2>> exists L2.
  
  Subgoal rev_acc_exists.2:
  
  Vars: L2:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  
  ==================================
  exists D1, {D1 : rev_acc nil L2 L2}
  
  rev_acc_exists.2>> exists rev_acc_nil L2.
  
  Subgoal rev_acc_exists.2:
  
  Vars: L2:o
  IH:
      forall L1, forall L2,
        {L1 : list}* =>
            {L2 : list} => exists L3, exists D1, {D1 : rev_acc L1 L2 L3}
  H2:{L2 : list}
  
  ==================================
  {rev_acc_nil L2 : rev_acc nil L2 L2}
  
  rev_acc_exists.2>> search.
  Proof Completed!
  
  >> Theorem rev_acc_rev_lem:
      forall  a B AB ba ba2 D1 D2 D3,
        {D1 : rev_acc a B AB} =>
          {D2 : rev_acc AB nil ba} =>
            {D3 : rev_acc B a ba2} => exists  D4, {D4 : eq_list ba ba2}.
  
  Subgoal rev_acc_rev_lem:
  
  
  ==================================
  forall a, forall B, forall AB, forall ba, forall ba2, forall D1, forall D2,
    forall D3,
    {D1 : rev_acc a B AB} =>
        {D2 : rev_acc AB nil ba} =>
            {D3 : rev_acc B a ba2} => exists D4, {D4 : eq_list ba ba2}
  
  rev_acc_rev_lem>> induction on 1.
  
  Subgoal rev_acc_rev_lem:
  
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
  
  rev_acc_rev_lem>> intros.
  
  Subgoal rev_acc_rev_lem:
  
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
  
  rev_acc_rev_lem>> cases H1.
  
  Subgoal rev_acc_rev_lem.1:
  
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
  
  Subgoal rev_acc_rev_lem.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  rev_acc_rev_lem.1>> assert exists  D4, {D4 : rev_acc cons N B L1 ba2}.
  
  Subgoal rev_acc_rev_lem.1:
  
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
  exists D4, {D4 : rev_acc (cons N B) L1 ba2}
  
  Subgoal rev_acc_rev_lem.1 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Subgoal rev_acc_rev_lem.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  rev_acc_rev_lem.1>> exists rev_acc_cons B L1 ba2 N D3.
  
  Subgoal rev_acc_rev_lem.1:
  
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
  {rev_acc_cons B L1 ba2 N D3 : rev_acc (cons N B) L1 ba2}
  
  Subgoal rev_acc_rev_lem.1 is:
   exists D4, {D4 : eq_list ba ba2}
  
  Subgoal rev_acc_rev_lem.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  rev_acc_rev_lem.1>> search.
  
  Subgoal rev_acc_rev_lem.1:
  
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
  H9:{D4 : rev_acc (cons N B) L1 ba2}
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Subgoal rev_acc_rev_lem.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  rev_acc_rev_lem.1>> apply IH to H8 H2 H9.
  
  Subgoal rev_acc_rev_lem.1:
  
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
  H9:{D4 : rev_acc (cons N B) L1 ba2}
  H10:{D1 : eq_list ba ba2}
  
  ==================================
  exists D4, {D4 : eq_list ba ba2}
  
  Subgoal rev_acc_rev_lem.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  rev_acc_rev_lem.1>> cases H10.
  
  Subgoal rev_acc_rev_lem.1:
  
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
  H9:{D4 : rev_acc (cons N B) L1 ba2}
  H11:{ba2 : list}
  
  ==================================
  exists D4, {D4 : eq_list ba2 ba2}
  
  Subgoal rev_acc_rev_lem.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  rev_acc_rev_lem.1>> exists refl_list ba2.
  
  Subgoal rev_acc_rev_lem.1:
  
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
  H9:{D4 : rev_acc (cons N B) L1 ba2}
  H11:{ba2 : list}
  
  ==================================
  {refl_list ba2 : eq_list ba2 ba2}
  
  Subgoal rev_acc_rev_lem.2 is:
   exists D4, {D4 : eq_list ba ba2}
  
  rev_acc_rev_lem.1>> search.
  
  Subgoal rev_acc_rev_lem.2:
  
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
  
  rev_acc_rev_lem.2>> apply rev_acc_func to H2 H3.
  
  Subgoal rev_acc_rev_lem.2:
  
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
  
  rev_acc_rev_lem.2>> exists D1.
  
  Subgoal rev_acc_rev_lem.2:
  
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
  
  rev_acc_rev_lem.2>> search.
  Proof Completed!
  
  >> Theorem rev_acc_rev:
      forall  L1 L2 D1,
        {D1 : rev_acc L1 nil L2} => exists  D2, {D2 : rev_acc L2 nil L1}.
  
  Subgoal rev_acc_rev:
  
  
  ==================================
  forall L1, forall L2, forall D1,
    {D1 : rev_acc L1 nil L2} => exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> intros.
  
  Subgoal rev_acc_rev:
  
  Vars: D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  
  ==================================
  exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> assert {L2 : list}.
  
  Subgoal rev_acc_rev:
  
  Vars: D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  
  ==================================
  exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> assert {nil : list}.
  
  Subgoal rev_acc_rev:
  
  Vars: D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  H3:{nil : list}
  
  ==================================
  exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> apply rev_acc_exists to H2 H3.
  
  Subgoal rev_acc_rev:
  
  Vars: D2:o, L3:o, D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  H3:{nil : list}
  H4:{D2 : rev_acc L2 nil L3}
  
  ==================================
  exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> assert exists  D3, {D3 : rev_acc nil L1 L1}.
  
  Subgoal rev_acc_rev:
  
  Vars: D2:o, L3:o, D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  H3:{nil : list}
  H4:{D2 : rev_acc L2 nil L3}
  
  ==================================
  exists D3, {D3 : rev_acc nil L1 L1}
  
  Subgoal rev_acc_rev is:
   exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> exists rev_acc_nil L1.
  
  Subgoal rev_acc_rev:
  
  Vars: D2:o, L3:o, D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  H3:{nil : list}
  H4:{D2 : rev_acc L2 nil L3}
  
  ==================================
  {rev_acc_nil L1 : rev_acc nil L1 L1}
  
  Subgoal rev_acc_rev is:
   exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> search.
  
  Subgoal rev_acc_rev:
  
  Vars: D3:o, D2:o, L3:o, D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  H3:{nil : list}
  H4:{D2 : rev_acc L2 nil L3}
  H5:{D3 : rev_acc nil L1 L1}
  
  ==================================
  exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> apply rev_acc_rev_lem to H1 H4 H5.
  
  Subgoal rev_acc_rev:
  
  Vars: D4:o, D3:o, D2:o, L3:o, D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  H3:{nil : list}
  H4:{D2 : rev_acc L2 nil L3}
  H5:{D3 : rev_acc nil L1 L1}
  H6:{D4 : eq_list L3 L1}
  
  ==================================
  exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> cases H6.
  
  Subgoal rev_acc_rev:
  
  Vars: D3:o, D2:o, D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  H3:{nil : list}
  H4:{D2 : rev_acc L2 nil L1}
  H5:{D3 : rev_acc nil L1 L1}
  H7:{L1 : list}
  
  ==================================
  exists D2, {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> exists D2.
  
  Subgoal rev_acc_rev:
  
  Vars: D3:o, D2:o, D1:o, L2:o, L1:o
  H1:{D1 : rev_acc L1 nil L2}
  H2:{L2 : list}
  H3:{nil : list}
  H4:{D2 : rev_acc L2 nil L1}
  H5:{D3 : rev_acc nil L1 L1}
  H7:{L1 : list}
  
  ==================================
  {D2 : rev_acc L2 nil L1}
  
  rev_acc_rev>> search.
  Proof Completed!
  
  >> Goodbye!
