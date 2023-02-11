  $ adelfa -i arith.ath
  Welcome!
  >> Specification arith.lf.
  
  >> Schema c := {}(x:nat).
  
  >> Theorem no_plus_one: forall  M1 M2 D, {D : plus s M1 M2 M1} => false.
  
  Subgoal no_plus_one:
  
  
  ==================================
  forall M1, forall M2, forall D, {D : plus (s M1) M2 M1} => False
  
  no_plus_one>> induction on 1.
  
  Subgoal no_plus_one:
  
  IH:forall M1, forall M2, forall D, {D : plus (s M1) M2 M1}* => False
  
  ==================================
  forall M1, forall M2, forall D, {D : plus (s M1) M2 M1}@ => False
  
  no_plus_one>> intros.
  
  Subgoal no_plus_one:
  
  Vars: D:o, M2:o, M1:o
  IH:forall M1, forall M2, forall D, {D : plus (s M1) M2 M1}* => False
  H1:{D : plus (s M1) M2 M1}@
  
  ==================================
  False
  
  no_plus_one>> cases H1.
  
  Subgoal no_plus_one:
  
  Vars: P:o, N3:o, M2:o
  IH:forall M1, forall M2, forall D, {D : plus (s M1) M2 M1}* => False
  H2:{s N3 : nat}*
  H3:{M2 : nat}*
  H4:{N3 : nat}*
  H5:{P : plus (s N3) M2 N3}*
  
  ==================================
  False
  
  no_plus_one>> apply IH to H5 with M1 = N3, M2 = M2, D = P.
  
  Subgoal no_plus_one:
  
  Vars: P:o, N3:o, M2:o
  IH:forall M1, forall M2, forall D, {D : plus (s M1) M2 M1}* => False
  H2:{s N3 : nat}*
  H3:{M2 : nat}*
  H4:{N3 : nat}*
  H5:{P : plus (s N3) M2 N3}*
  H6:False
  
  ==================================
  False
  
  no_plus_one>> search.
  Proof Completed!
  
  >> Theorem z_nat: ctx  G:c, {G |- z : nat} => false => false.
  
  Subgoal z_nat:
  
  
  ==================================
  ctx G:c, {G |- z : nat} => False => False
  
  z_nat>> intros.
  
  Subgoal z_nat:
  
  H1:ctx G:c, {G |- z : nat} => False
  
  ==================================
  False
  
  z_nat>> assert {z : nat}.
  
  Subgoal z_nat:
  
  H1:ctx G:c, {G |- z : nat} => False
  H2:{z : nat}
  
  ==================================
  False
  
  z_nat>> apply H1 to H2.
  
  Subgoal z_nat:
  
  H1:ctx G:c, {G |- z : nat} => False
  H2:{z : nat}
  H3:False
  
  ==================================
  False
  
  z_nat>> cases H3.
  Proof Completed!
  
  >> Theorem plus_n_z: forall  N, {N : nat} => exists  D, {D : plus N z N}.
  
  Subgoal plus_n_z:
  
  
  ==================================
  forall N, {N : nat} => exists D, {D : plus N z N}
  
  plus_n_z>> induction on 1.
  
  Subgoal plus_n_z:
  
  IH:forall N, {N : nat}* => exists D, {D : plus N z N}
  
  ==================================
  forall N, {N : nat}@ => exists D, {D : plus N z N}
  
  plus_n_z>> intros.
  
  Subgoal plus_n_z:
  
  Vars: N:o
  IH:forall N, {N : nat}* => exists D, {D : plus N z N}
  H1:{N : nat}@
  
  ==================================
  exists D, {D : plus N z N}
  
  plus_n_z>> cases H1.
  
  Subgoal plus_n_z.1:
  
  Vars: x:o
  IH:forall N, {N : nat}* => exists D, {D : plus N z N}
  H2:{x : nat}*
  
  ==================================
  exists D, {D : plus (s x) z (s x)}
  
  Subgoal plus_n_z.2 is:
   exists D, {D : plus z z z}
  
  plus_n_z.1>> apply IH to H2 with N = x.
  
  Subgoal plus_n_z.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : plus N z N}
  H2:{x : nat}*
  H3:{D : plus x z x}
  
  ==================================
  exists D, {D : plus (s x) z (s x)}
  
  Subgoal plus_n_z.2 is:
   exists D, {D : plus z z z}
  
  plus_n_z.1>> exists plus_s x z x D.
  
  Subgoal plus_n_z.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : plus N z N}
  H2:{x : nat}*
  H3:{D : plus x z x}
  
  ==================================
  {plus_s x z x D : plus (s x) z (s x)}
  
  Subgoal plus_n_z.2 is:
   exists D, {D : plus z z z}
  
  plus_n_z.1>> search.
  
  Subgoal plus_n_z.2:
  
  IH:forall N, {N : nat}* => exists D, {D : plus N z N}
  
  ==================================
  exists D, {D : plus z z z}
  
  plus_n_z.2>> exists plus_z z.
  
  Subgoal plus_n_z.2:
  
  IH:forall N, {N : nat}* => exists D, {D : plus N z N}
  
  ==================================
  {plus_z z : plus z z z}
  
  plus_n_z.2>> search.
  Proof Completed!
  
  >> Theorem identity:
      exists  X,
        {X : nat} => forall  Y, {Y : nat} => exists  D, {D : mult X Y Y}.
  
  Subgoal identity:
  
  
  ==================================
  exists X, {X : nat} => forall Y, {Y : nat} => exists D, {D : mult X Y Y}
  
  identity>> exists s z.
  
  Subgoal identity:
  
  
  ==================================
  {s z : nat} => forall Y, {Y : nat} => exists D, {D : mult (s z) Y Y}
  
  identity>> intros.
  
  Subgoal identity:
  
  Vars: Y:o
  H1:{s z : nat}
  H2:{Y : nat}
  
  ==================================
  exists D, {D : mult (s z) Y Y}
  
  identity>> apply plus_n_z to H2.
  
  Subgoal identity:
  
  Vars: D:o, Y:o
  H1:{s z : nat}
  H2:{Y : nat}
  H3:{D : plus Y z Y}
  
  ==================================
  exists D, {D : mult (s z) Y Y}
  
  identity>> exists mult_s z Y z Y mult_z Y D.
  
  Subgoal identity:
  
  Vars: D:o, Y:o
  H1:{s z : nat}
  H2:{Y : nat}
  H3:{D : plus Y z Y}
  
  ==================================
  {mult_s z Y z Y (mult_z Y) D : mult (s z) Y Y}
  
  identity>> search.
  Proof Completed!
  
  >> Theorem old_plus_n_s:
      forall  N1,
        {N1 : nat} =>
          forall  N2,
            {N2 : nat} =>
              forall  N3,
                {N3 : nat} =>
                  forall  D,
                    {D : plus N1 N2 N3} => exists  D1, {D1 : plus N1 s N2 s N3}.
  
  Subgoal old_plus_n_s:
  
  
  ==================================
  forall N1,
    {N1 : nat} =>
        forall N2,
          {N2 : nat} =>
              forall N3,
                {N3 : nat} =>
                    forall D,
                      {D : plus N1 N2 N3} =>
                          exists D1, {D1 : plus N1 (s N2) (s N3)}
  
  old_plus_n_s>> induction on 4.
  
  Subgoal old_plus_n_s:
  
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  
  ==================================
  forall N1,
    {N1 : nat} =>
        forall N2,
          {N2 : nat} =>
              forall N3,
                {N3 : nat} =>
                    forall D,
                      {D : plus N1 N2 N3}@ =>
                          exists D1, {D1 : plus N1 (s N2) (s N3)}
  
  old_plus_n_s>> intros.
  
  Subgoal old_plus_n_s:
  
  Vars: D:o, N3:o, N2:o, N1:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{N1 : nat}
  H2:{N2 : nat}
  H3:{N3 : nat}
  H4:{D : plus N1 N2 N3}@
  
  ==================================
  exists D1, {D1 : plus N1 (s N2) (s N3)}
  
  old_plus_n_s>> cases H4.
  
  Subgoal old_plus_n_s.1:
  
  Vars: P:o, N4:o, N6:o, N2:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{s N4 : nat}
  H2:{N2 : nat}
  H3:{s N6 : nat}
  H5:{N4 : nat}*
  H6:{N2 : nat}*
  H7:{N6 : nat}*
  H8:{P : plus N4 N2 N6}*
  
  ==================================
  exists D1, {D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal old_plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  old_plus_n_s.1>> apply IH to H5.
  
  Subgoal old_plus_n_s.1:
  
  Vars: P:o, N4:o, N6:o, N2:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{s N4 : nat}
  H2:{N2 : nat}
  H3:{s N6 : nat}
  H5:{N4 : nat}*
  H6:{N2 : nat}*
  H7:{N6 : nat}*
  H8:{P : plus N4 N2 N6}*
  H9:
      forall N2,
        {N2 : nat} =>
            forall N3,
              {N3 : nat} =>
                  forall D,
                    {D : plus N4 N2 N3}* =>
                        exists D1, {D1 : plus N4 (s N2) (s N3)}
  
  ==================================
  exists D1, {D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal old_plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  old_plus_n_s.1>> apply H9 to H6.
  
  Subgoal old_plus_n_s.1:
  
  Vars: P:o, N4:o, N6:o, N2:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{s N4 : nat}
  H2:{N2 : nat}
  H3:{s N6 : nat}
  H5:{N4 : nat}*
  H6:{N2 : nat}*
  H7:{N6 : nat}*
  H8:{P : plus N4 N2 N6}*
  H9:
      forall N2,
        {N2 : nat} =>
            forall N3,
              {N3 : nat} =>
                  forall D,
                    {D : plus N4 N2 N3}* =>
                        exists D1, {D1 : plus N4 (s N2) (s N3)}
  H10:
      forall N3,
        {N3 : nat} =>
            forall D,
              {D : plus N4 N2 N3}* => exists D1, {D1 : plus N4 (s N2) (s N3)}
  
  ==================================
  exists D1, {D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal old_plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  old_plus_n_s.1>> apply H10 to H7.
  
  Subgoal old_plus_n_s.1:
  
  Vars: P:o, N4:o, N6:o, N2:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{s N4 : nat}
  H2:{N2 : nat}
  H3:{s N6 : nat}
  H5:{N4 : nat}*
  H6:{N2 : nat}*
  H7:{N6 : nat}*
  H8:{P : plus N4 N2 N6}*
  H9:
      forall N2,
        {N2 : nat} =>
            forall N3,
              {N3 : nat} =>
                  forall D,
                    {D : plus N4 N2 N3}* =>
                        exists D1, {D1 : plus N4 (s N2) (s N3)}
  H10:
      forall N3,
        {N3 : nat} =>
            forall D,
              {D : plus N4 N2 N3}* => exists D1, {D1 : plus N4 (s N2) (s N3)}
  H11:forall D, {D : plus N4 N2 N6}* => exists D1, {D1 : plus N4 (s N2) (s N6)}
  
  ==================================
  exists D1, {D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal old_plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  old_plus_n_s.1>> apply H11 to H8.
  
  Subgoal old_plus_n_s.1:
  
  Vars: D1:o, P:o, N4:o, N6:o, N2:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{s N4 : nat}
  H2:{N2 : nat}
  H3:{s N6 : nat}
  H5:{N4 : nat}*
  H6:{N2 : nat}*
  H7:{N6 : nat}*
  H8:{P : plus N4 N2 N6}*
  H9:
      forall N2,
        {N2 : nat} =>
            forall N3,
              {N3 : nat} =>
                  forall D,
                    {D : plus N4 N2 N3}* =>
                        exists D1, {D1 : plus N4 (s N2) (s N3)}
  H10:
      forall N3,
        {N3 : nat} =>
            forall D,
              {D : plus N4 N2 N3}* => exists D1, {D1 : plus N4 (s N2) (s N3)}
  H11:forall D, {D : plus N4 N2 N6}* => exists D1, {D1 : plus N4 (s N2) (s N6)}
  H12:{D1 : plus N4 (s N2) (s N6)}
  
  ==================================
  exists D1, {D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal old_plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  old_plus_n_s.1>> exists plus_s N4 s N2 s N6 D1.
  
  Subgoal old_plus_n_s.1:
  
  Vars: D1:o, P:o, N4:o, N6:o, N2:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{s N4 : nat}
  H2:{N2 : nat}
  H3:{s N6 : nat}
  H5:{N4 : nat}*
  H6:{N2 : nat}*
  H7:{N6 : nat}*
  H8:{P : plus N4 N2 N6}*
  H9:
      forall N2,
        {N2 : nat} =>
            forall N3,
              {N3 : nat} =>
                  forall D,
                    {D : plus N4 N2 N3}* =>
                        exists D1, {D1 : plus N4 (s N2) (s N3)}
  H10:
      forall N3,
        {N3 : nat} =>
            forall D,
              {D : plus N4 N2 N3}* => exists D1, {D1 : plus N4 (s N2) (s N3)}
  H11:forall D, {D : plus N4 N2 N6}* => exists D1, {D1 : plus N4 (s N2) (s N6)}
  H12:{D1 : plus N4 (s N2) (s N6)}
  
  ==================================
  {plus_s N4 (s N2) (s N6) D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal old_plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  old_plus_n_s.1>> search.
  
  Subgoal old_plus_n_s.2:
  
  Vars: N3:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{z : nat}
  H2:{N3 : nat}
  H3:{N3 : nat}
  H5:{N3 : nat}*
  
  ==================================
  exists D1, {D1 : plus z (s N3) (s N3)}
  
  old_plus_n_s.2>> exists plus_z s N3.
  
  Subgoal old_plus_n_s.2:
  
  Vars: N3:o
  IH:
      forall N1,
        {N1 : nat} =>
            forall N2,
              {N2 : nat} =>
                  forall N3,
                    {N3 : nat} =>
                        forall D,
                          {D : plus N1 N2 N3}* =>
                              exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{z : nat}
  H2:{N3 : nat}
  H3:{N3 : nat}
  H5:{N3 : nat}*
  
  ==================================
  {plus_z (s N3) : plus z (s N3) (s N3)}
  
  old_plus_n_s.2>> search.
  Proof Completed!
  
  >> Theorem plus_n_s:
      forall  N1 N2 N3 D,
        {D : plus N1 N2 N3} => exists  D1, {D1 : plus N1 s N2 s N3}.
  
  Subgoal plus_n_s:
  
  
  ==================================
  forall N1, forall N2, forall N3, forall D,
    {D : plus N1 N2 N3} => exists D1, {D1 : plus N1 (s N2) (s N3)}
  
  plus_n_s>> induction on 1.
  
  Subgoal plus_n_s:
  
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N1 (s N2) (s N3)}
  
  ==================================
  forall N1, forall N2, forall N3, forall D,
    {D : plus N1 N2 N3}@ => exists D1, {D1 : plus N1 (s N2) (s N3)}
  
  plus_n_s>> intros.
  
  Subgoal plus_n_s:
  
  Vars: D:o, N3:o, N2:o, N1:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N1 (s N2) (s N3)}
  H1:{D : plus N1 N2 N3}@
  
  ==================================
  exists D1, {D1 : plus N1 (s N2) (s N3)}
  
  plus_n_s>> cases H1.
  
  Subgoal plus_n_s.1:
  
  Vars: P:o, N4:o, N6:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N1 (s N2) (s N3)}
  H2:{N4 : nat}*
  H3:{N2 : nat}*
  H4:{N6 : nat}*
  H5:{P : plus N4 N2 N6}*
  
  ==================================
  exists D1, {D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  plus_n_s.1>> apply IH to H5.
  
  Subgoal plus_n_s.1:
  
  Vars: D1:o, P:o, N4:o, N6:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N1 (s N2) (s N3)}
  H2:{N4 : nat}*
  H3:{N2 : nat}*
  H4:{N6 : nat}*
  H5:{P : plus N4 N2 N6}*
  H6:{D1 : plus N4 (s N2) (s N6)}
  
  ==================================
  exists D1, {D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  plus_n_s.1>> exists plus_s N4 s N2 s N6 D1.
  
  Subgoal plus_n_s.1:
  
  Vars: D1:o, P:o, N4:o, N6:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N1 (s N2) (s N3)}
  H2:{N4 : nat}*
  H3:{N2 : nat}*
  H4:{N6 : nat}*
  H5:{P : plus N4 N2 N6}*
  H6:{D1 : plus N4 (s N2) (s N6)}
  
  ==================================
  {plus_s N4 (s N2) (s N6) D1 : plus (s N4) (s N2) (s (s N6))}
  
  Subgoal plus_n_s.2 is:
   exists D1, {D1 : plus z (s N3) (s N3)}
  
  plus_n_s.1>> search.
  
  Subgoal plus_n_s.2:
  
  Vars: N3:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N1 (s N2) (s N3)}
  H2:{N3 : nat}*
  
  ==================================
  exists D1, {D1 : plus z (s N3) (s N3)}
  
  plus_n_s.2>> exists plus_z s N3.
  
  Subgoal plus_n_s.2:
  
  Vars: N3:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N1 (s N2) (s N3)}
  H2:{N3 : nat}*
  
  ==================================
  {plus_z (s N3) : plus z (s N3) (s N3)}
  
  plus_n_s.2>> search.
  Proof Completed!
  
  >> Theorem plus_comm:
      forall  N1 N2 N3 D,
        {D : plus N1 N2 N3} => exists  D1, {D1 : plus N2 N1 N3}.
  
  Subgoal plus_comm:
  
  
  ==================================
  forall N1, forall N2, forall N3, forall D,
    {D : plus N1 N2 N3} => exists D1, {D1 : plus N2 N1 N3}
  
  plus_comm>> induction on 1.
  
  Subgoal plus_comm:
  
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  
  ==================================
  forall N1, forall N2, forall N3, forall D,
    {D : plus N1 N2 N3}@ => exists D1, {D1 : plus N2 N1 N3}
  
  plus_comm>> intros.
  
  Subgoal plus_comm:
  
  Vars: D:o, N3:o, N2:o, N1:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  H1:{D : plus N1 N2 N3}@
  
  ==================================
  exists D1, {D1 : plus N2 N1 N3}
  
  plus_comm>> cases H1.
  
  Subgoal plus_comm.1:
  
  Vars: P:o, N4:o, N6:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  H2:{N4 : nat}*
  H3:{N2 : nat}*
  H4:{N6 : nat}*
  H5:{P : plus N4 N2 N6}*
  
  ==================================
  exists D1, {D1 : plus N2 (s N4) (s N6)}
  
  Subgoal plus_comm.2 is:
   exists D1, {D1 : plus N3 z N3}
  
  plus_comm.1>> apply IH to H5.
  
  Subgoal plus_comm.1:
  
  Vars: D1:o, P:o, N4:o, N6:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  H2:{N4 : nat}*
  H3:{N2 : nat}*
  H4:{N6 : nat}*
  H5:{P : plus N4 N2 N6}*
  H6:{D1 : plus N2 N4 N6}
  
  ==================================
  exists D1, {D1 : plus N2 (s N4) (s N6)}
  
  Subgoal plus_comm.2 is:
   exists D1, {D1 : plus N3 z N3}
  
  plus_comm.1>> apply plus_n_s to H6.
  
  Subgoal plus_comm.1:
  
  Vars: D2:o, D1:o, P:o, N4:o, N6:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  H2:{N4 : nat}*
  H3:{N2 : nat}*
  H4:{N6 : nat}*
  H5:{P : plus N4 N2 N6}*
  H6:{D1 : plus N2 N4 N6}
  H7:{D2 : plus N2 (s N4) (s N6)}
  
  ==================================
  exists D1, {D1 : plus N2 (s N4) (s N6)}
  
  Subgoal plus_comm.2 is:
   exists D1, {D1 : plus N3 z N3}
  
  plus_comm.1>> exists D2.
  
  Subgoal plus_comm.1:
  
  Vars: D2:o, D1:o, P:o, N4:o, N6:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  H2:{N4 : nat}*
  H3:{N2 : nat}*
  H4:{N6 : nat}*
  H5:{P : plus N4 N2 N6}*
  H6:{D1 : plus N2 N4 N6}
  H7:{D2 : plus N2 (s N4) (s N6)}
  
  ==================================
  {D2 : plus N2 (s N4) (s N6)}
  
  Subgoal plus_comm.2 is:
   exists D1, {D1 : plus N3 z N3}
  
  plus_comm.1>> search.
  
  Subgoal plus_comm.2:
  
  Vars: N3:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  H2:{N3 : nat}*
  
  ==================================
  exists D1, {D1 : plus N3 z N3}
  
  plus_comm.2>> apply plus_n_z to H2.
  
  Subgoal plus_comm.2:
  
  Vars: D:o, N3:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  H2:{N3 : nat}*
  H3:{D : plus N3 z N3}
  
  ==================================
  exists D1, {D1 : plus N3 z N3}
  
  plus_comm.2>> exists D.
  
  Subgoal plus_comm.2:
  
  Vars: D:o, N3:o
  IH:
      forall N1, forall N2, forall N3, forall D,
        {D : plus N1 N2 N3}* => exists D1, {D1 : plus N2 N1 N3}
  H2:{N3 : nat}*
  H3:{D : plus N3 z N3}
  
  ==================================
  {D : plus N3 z N3}
  
  plus_comm.2>> search.
  Proof Completed!
  
  >> Theorem plus_s_n:
      forall  N1 N2 N3 D,
        {D : plus N1 N2 N3} => exists  D1, {D1 : plus s N1 N2 s N3}.
  
  Subgoal plus_s_n:
  
  
  ==================================
  forall N1, forall N2, forall N3, forall D,
    {D : plus N1 N2 N3} => exists D1, {D1 : plus (s N1) N2 (s N3)}
  
  plus_s_n>> intros.
  
  Subgoal plus_s_n:
  
  Vars: D:o, N3:o, N2:o, N1:o
  H1:{D : plus N1 N2 N3}
  
  ==================================
  exists D1, {D1 : plus (s N1) N2 (s N3)}
  
  plus_s_n>> exists plus_s N1 N2 N3 D.
  
  Subgoal plus_s_n:
  
  Vars: D:o, N3:o, N2:o, N1:o
  H1:{D : plus N1 N2 N3}
  
  ==================================
  {plus_s N1 N2 N3 D : plus (s N1) N2 (s N3)}
  
  plus_s_n>> cases H1.
  
  Subgoal plus_s_n.1:
  
  Vars: P:o, N4:o, N6:o, N2:o
  H2:{N4 : nat}
  H3:{N2 : nat}
  H4:{N6 : nat}
  H5:{P : plus N4 N2 N6}
  
  ==================================
  {plus_s (s N4) N2 (s N6) (plus_s N4 N2 N6 P) : plus (s (s N4)) N2 (s (s N6))}
  
  Subgoal plus_s_n.2 is:
   {plus_s z N3 N3 (plus_z N3) : plus (s z) N3 (s N3)}
  
  plus_s_n.1>> search.
  
  Subgoal plus_s_n.2:
  
  Vars: N3:o
  H2:{N3 : nat}
  
  ==================================
  {plus_s z N3 N3 (plus_z N3) : plus (s z) N3 (s N3)}
  
  plus_s_n.2>> search.
  Proof Completed!
  
  >> Theorem plus_func:
      forall  N1 N2,
        {N1 : nat} => {N2 : nat} => exists  N3 D, {D : plus N1 N2 N3}.
  
  Subgoal plus_func:
  
  
  ==================================
  forall N1, forall N2,
    {N1 : nat} => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  
  plus_func>> induction on 1.
  
  Subgoal plus_func:
  
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  
  ==================================
  forall N1, forall N2,
    {N1 : nat}@ => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  
  plus_func>> intros.
  
  Subgoal plus_func:
  
  Vars: N2:o, N1:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H1:{N1 : nat}@
  H2:{N2 : nat}
  
  ==================================
  exists N3, exists D, {D : plus N1 N2 N3}
  
  plus_func>> cases H1.
  
  Subgoal plus_func.1:
  
  Vars: x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  
  ==================================
  exists N3, exists D, {D : plus (s x) N2 N3}
  
  Subgoal plus_func.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus_func.1>> apply IH to H3 H2 with N1 = x, N2 = N2.
  
  Subgoal plus_func.1:
  
  Vars: D:o, N3:o, x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  H4:{D : plus x N2 N3}
  
  ==================================
  exists N3, exists D, {D : plus (s x) N2 N3}
  
  Subgoal plus_func.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus_func.1>> exists s N3.
  
  Subgoal plus_func.1:
  
  Vars: D:o, N3:o, x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  H4:{D : plus x N2 N3}
  
  ==================================
  exists D, {D : plus (s x) N2 (s N3)}
  
  Subgoal plus_func.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus_func.1>> exists plus_s x N2 N3 D.
  
  Subgoal plus_func.1:
  
  Vars: D:o, N3:o, x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  H4:{D : plus x N2 N3}
  
  ==================================
  {plus_s x N2 N3 D : plus (s x) N2 (s N3)}
  
  Subgoal plus_func.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus_func.1>> assert {N3 : nat}.
  
  Subgoal plus_func.1:
  
  Vars: D:o, N3:o, x:o, N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  H3:{x : nat}*
  H4:{D : plus x N2 N3}
  H5:{N3 : nat}
  
  ==================================
  {plus_s x N2 N3 D : plus (s x) N2 (s N3)}
  
  Subgoal plus_func.2 is:
   exists N3, exists D, {D : plus z N2 N3}
  
  plus_func.1>> search.
  
  Subgoal plus_func.2:
  
  Vars: N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  
  ==================================
  exists N3, exists D, {D : plus z N2 N3}
  
  plus_func.2>> exists N2.
  
  Subgoal plus_func.2:
  
  Vars: N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  
  ==================================
  exists D, {D : plus z N2 N2}
  
  plus_func.2>> exists plus_z N2.
  
  Subgoal plus_func.2:
  
  Vars: N2:o
  IH:
      forall N1, forall N2,
        {N1 : nat}* => {N2 : nat} => exists N3, exists D, {D : plus N1 N2 N3}
  H2:{N2 : nat}
  
  ==================================
  {plus_z N2 : plus z N2 N2}
  
  plus_func.2>> search.
  Proof Completed!
  
  >> Theorem plus_func2:
      forall  N1 N2 N3 N4 D1 D2,
        {D1 : plus N1 N2 N3} =>
          {D2 : plus N1 N2 N4} => exists  D, {D : eq N3 N4}.
  
  Subgoal plus_func2:
  
  
  ==================================
  forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
    {D1 : plus N1 N2 N3} => {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  
  plus_func2>> induction on 1.
  
  Subgoal plus_func2:
  
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  
  ==================================
  forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
    {D1 : plus N1 N2 N3}@ => {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  
  plus_func2>> intros.
  
  Subgoal plus_func2:
  
  Vars: D2:o, D1:o, N4:o, N3:o, N2:o, N1:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H1:{D1 : plus N1 N2 N3}@
  H2:{D2 : plus N1 N2 N4}
  
  ==================================
  exists D, {D : eq N3 N4}
  
  plus_func2>> cases H1.
  
  Subgoal plus_func2.1:
  
  Vars: P:o, N5:o, N7:o, D2:o, N4:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H2:{D2 : plus (s N5) N2 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N7 : nat}*
  H6:{P : plus N5 N2 N7}*
  
  ==================================
  exists D, {D : eq (s N7) N4}
  
  Subgoal plus_func2.2 is:
   exists D, {D : eq N3 N4}
  
  plus_func2.1>> cases H2.
  
  Subgoal plus_func2.1:
  
  Vars: P1:o, N9:o, P:o, N5:o, N7:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N7 : nat}*
  H6:{P : plus N5 N2 N7}*
  H7:{N5 : nat}
  H8:{N2 : nat}
  H9:{N9 : nat}
  H10:{P1 : plus N5 N2 N9}
  
  ==================================
  exists D, {D : eq (s N7) (s N9)}
  
  Subgoal plus_func2.2 is:
   exists D, {D : eq N3 N4}
  
  plus_func2.1>> apply IH to H6 H10 with N1 = N5, N2 = N2, N3 = N7, N4 = N9, D1 = P, D2 = P1.
  
  Subgoal plus_func2.1:
  
  Vars: D:o, P1:o, N9:o, P:o, N5:o, N7:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N7 : nat}*
  H6:{P : plus N5 N2 N7}*
  H7:{N5 : nat}
  H8:{N2 : nat}
  H9:{N9 : nat}
  H10:{P1 : plus N5 N2 N9}
  H11:{D : eq N7 N9}
  
  ==================================
  exists D, {D : eq (s N7) (s N9)}
  
  Subgoal plus_func2.2 is:
   exists D, {D : eq N3 N4}
  
  plus_func2.1>> cases H11.
  
  Subgoal plus_func2.1:
  
  Vars: P1:o, N9:o, P:o, N5:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N9 : nat}*
  H6:{P : plus N5 N2 N9}*
  H7:{N5 : nat}
  H8:{N2 : nat}
  H9:{N9 : nat}
  H10:{P1 : plus N5 N2 N9}
  H12:{N9 : nat}
  
  ==================================
  exists D, {D : eq (s N9) (s N9)}
  
  Subgoal plus_func2.2 is:
   exists D, {D : eq N3 N4}
  
  plus_func2.1>> exists refl s N9.
  
  Subgoal plus_func2.1:
  
  Vars: P1:o, N9:o, P:o, N5:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N9 : nat}*
  H6:{P : plus N5 N2 N9}*
  H7:{N5 : nat}
  H8:{N2 : nat}
  H9:{N9 : nat}
  H10:{P1 : plus N5 N2 N9}
  H12:{N9 : nat}
  
  ==================================
  {refl (s N9) : eq (s N9) (s N9)}
  
  Subgoal plus_func2.2 is:
   exists D, {D : eq N3 N4}
  
  plus_func2.1>> search.
  
  Subgoal plus_func2.2:
  
  Vars: D2:o, N4:o, N3:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H2:{D2 : plus z N3 N4}
  H3:{N3 : nat}*
  
  ==================================
  exists D, {D : eq N3 N4}
  
  plus_func2.2>> cases H2.
  
  Subgoal plus_func2.2:
  
  Vars: N4:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H3:{N4 : nat}*
  H4:{N4 : nat}
  
  ==================================
  exists D, {D : eq N4 N4}
  
  plus_func2.2>> exists refl N4.
  
  Subgoal plus_func2.2:
  
  Vars: N4:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : plus N1 N2 N3}* =>
            {D2 : plus N1 N2 N4} => exists D, {D : eq N3 N4}
  H3:{N4 : nat}*
  H4:{N4 : nat}
  
  ==================================
  {refl N4 : eq N4 N4}
  
  plus_func2.2>> search.
  Proof Completed!
  
  >> Theorem plus_ident:
      exists  I, forall  N, {N : nat} => exists  D, {D : plus I N N}.
  
  Subgoal plus_ident:
  
  
  ==================================
  exists I, forall N, {N : nat} => exists D, {D : plus I N N}
  
  plus_ident>> exists z.
  
  Subgoal plus_ident:
  
  
  ==================================
  forall N, {N : nat} => exists D, {D : plus z N N}
  
  plus_ident>> intros.
  
  Subgoal plus_ident:
  
  Vars: N:o
  H1:{N : nat}
  
  ==================================
  exists D, {D : plus z N N}
  
  plus_ident>> exists plus_z N.
  
  Subgoal plus_ident:
  
  Vars: N:o
  H1:{N : nat}
  
  ==================================
  {plus_z N : plus z N N}
  
  plus_ident>> search.
  Proof Completed!
  
  >> Theorem plus_ident_com:
      exists  I, forall  N, {N : nat} => exists  D, {D : plus N I N}.
  
  Subgoal plus_ident_com:
  
  
  ==================================
  exists I, forall N, {N : nat} => exists D, {D : plus N I N}
  
  plus_ident_com>> exists z.
  
  Subgoal plus_ident_com:
  
  
  ==================================
  forall N, {N : nat} => exists D, {D : plus N z N}
  
  plus_ident_com>> intros.
  
  Subgoal plus_ident_com:
  
  Vars: N:o
  H1:{N : nat}
  
  ==================================
  exists D, {D : plus N z N}
  
  plus_ident_com>> apply plus_n_z to H1.
  
  Subgoal plus_ident_com:
  
  Vars: D:o, N:o
  H1:{N : nat}
  H2:{D : plus N z N}
  
  ==================================
  exists D, {D : plus N z N}
  
  plus_ident_com>> exists D.
  
  Subgoal plus_ident_com:
  
  Vars: D:o, N:o
  H1:{N : nat}
  H2:{D : plus N z N}
  
  ==================================
  {D : plus N z N}
  
  plus_ident_com>> search.
  Proof Completed!
  
  >> Theorem mult_ident:
      exists  I, forall  N, {N : nat} => exists  D, {D : mult I N N}.
  
  Subgoal mult_ident:
  
  
  ==================================
  exists I, forall N, {N : nat} => exists D, {D : mult I N N}
  
  mult_ident>> exists s z.
  
  Subgoal mult_ident:
  
  
  ==================================
  forall N, {N : nat} => exists D, {D : mult (s z) N N}
  
  mult_ident>> intros.
  
  Subgoal mult_ident:
  
  Vars: N:o
  H1:{N : nat}
  
  ==================================
  exists D, {D : mult (s z) N N}
  
  mult_ident>> assert exists  D1, {D1 : plus N z N}.
  
  Subgoal mult_ident:
  
  Vars: N:o
  H1:{N : nat}
  
  ==================================
  exists D1, {D1 : plus N z N}
  
  Subgoal mult_ident is:
   exists D, {D : mult (s z) N N}
  
  mult_ident>> apply plus_n_z to H1 with N = N.
  
  Subgoal mult_ident:
  
  Vars: D:o, N:o
  H1:{N : nat}
  H2:{D : plus N z N}
  
  ==================================
  exists D1, {D1 : plus N z N}
  
  Subgoal mult_ident is:
   exists D, {D : mult (s z) N N}
  
  mult_ident>> exists D.
  
  Subgoal mult_ident:
  
  Vars: D:o, N:o
  H1:{N : nat}
  H2:{D : plus N z N}
  
  ==================================
  {D : plus N z N}
  
  Subgoal mult_ident is:
   exists D, {D : mult (s z) N N}
  
  mult_ident>> search.
  
  Subgoal mult_ident:
  
  Vars: D1:o, N:o
  H1:{N : nat}
  H2:{D1 : plus N z N}
  
  ==================================
  exists D, {D : mult (s z) N N}
  
  mult_ident>> exists mult_s z N z N mult_z N D1.
  
  Subgoal mult_ident:
  
  Vars: D1:o, N:o
  H1:{N : nat}
  H2:{D1 : plus N z N}
  
  ==================================
  {mult_s z N z N (mult_z N) D1 : mult (s z) N N}
  
  mult_ident>> search.
  Proof Completed!
  
  >> Theorem mult_n_z: forall  N, {N : nat} => exists  D, {D : mult N z z}.
  
  Subgoal mult_n_z:
  
  
  ==================================
  forall N, {N : nat} => exists D, {D : mult N z z}
  
  mult_n_z>> induction on 1.
  
  Subgoal mult_n_z:
  
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  
  ==================================
  forall N, {N : nat}@ => exists D, {D : mult N z z}
  
  mult_n_z>> intros.
  
  Subgoal mult_n_z:
  
  Vars: N:o
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  H1:{N : nat}@
  
  ==================================
  exists D, {D : mult N z z}
  
  mult_n_z>> cases H1.
  
  Subgoal mult_n_z.1:
  
  Vars: x:o
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  H2:{x : nat}*
  
  ==================================
  exists D, {D : mult (s x) z z}
  
  Subgoal mult_n_z.2 is:
   exists D, {D : mult z z z}
  
  mult_n_z.1>> apply IH to H2 with N = x.
  
  Subgoal mult_n_z.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  H2:{x : nat}*
  H3:{D : mult x z z}
  
  ==================================
  exists D, {D : mult (s x) z z}
  
  Subgoal mult_n_z.2 is:
   exists D, {D : mult z z z}
  
  mult_n_z.1>> assert exists  D1, {D1 : plus z z z}.
  
  Subgoal mult_n_z.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  H2:{x : nat}*
  H3:{D : mult x z z}
  
  ==================================
  exists D1, {D1 : plus z z z}
  
  Subgoal mult_n_z.1 is:
   exists D, {D : mult (s x) z z}
  
  Subgoal mult_n_z.2 is:
   exists D, {D : mult z z z}
  
  mult_n_z.1>> exists plus_z z.
  
  Subgoal mult_n_z.1:
  
  Vars: D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  H2:{x : nat}*
  H3:{D : mult x z z}
  
  ==================================
  {plus_z z : plus z z z}
  
  Subgoal mult_n_z.1 is:
   exists D, {D : mult (s x) z z}
  
  Subgoal mult_n_z.2 is:
   exists D, {D : mult z z z}
  
  mult_n_z.1>> search.
  
  Subgoal mult_n_z.1:
  
  Vars: D1:o, D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  H2:{x : nat}*
  H3:{D : mult x z z}
  H4:{D1 : plus z z z}
  
  ==================================
  exists D, {D : mult (s x) z z}
  
  Subgoal mult_n_z.2 is:
   exists D, {D : mult z z z}
  
  mult_n_z.1>> exists mult_s x z z z D D1.
  
  Subgoal mult_n_z.1:
  
  Vars: D1:o, D:o, x:o
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  H2:{x : nat}*
  H3:{D : mult x z z}
  H4:{D1 : plus z z z}
  
  ==================================
  {mult_s x z z z D D1 : mult (s x) z z}
  
  Subgoal mult_n_z.2 is:
   exists D, {D : mult z z z}
  
  mult_n_z.1>> search.
  
  Subgoal mult_n_z.2:
  
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  
  ==================================
  exists D, {D : mult z z z}
  
  mult_n_z.2>> exists mult_z z.
  
  Subgoal mult_n_z.2:
  
  IH:forall N, {N : nat}* => exists D, {D : mult N z z}
  
  ==================================
  {mult_z z : mult z z z}
  
  mult_n_z.2>> search.
  Proof Completed!
  
  >> Theorem mult_func:
      forall  N1 N2 N3 N4 D1 D2,
        {D1 : mult N1 N2 N3} =>
          {D2 : mult N1 N2 N4} => exists  D3, {D3 : eq N3 N4}.
  
  Subgoal mult_func:
  
  
  ==================================
  forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
    {D1 : mult N1 N2 N3} => {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  
  mult_func>> induction on 1.
  
  Subgoal mult_func:
  
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  
  ==================================
  forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
    {D1 : mult N1 N2 N3}@ => {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  
  mult_func>> intros.
  
  Subgoal mult_func:
  
  Vars: D2:o, D1:o, N4:o, N3:o, N2:o, N1:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H1:{D1 : mult N1 N2 N3}@
  H2:{D2 : mult N1 N2 N4}
  
  ==================================
  exists D3, {D3 : eq N3 N4}
  
  mult_func>> cases H1.
  
  Subgoal mult_func.1:
  
  Vars: N7:o, M:o, P:o, N5:o, D2:o, N4:o, N3:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H2:{D2 : mult (s N5) N2 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N7 : nat}*
  H6:{N3 : nat}*
  H7:{M : mult N5 N2 N7}*
  H8:{P : plus N2 N7 N3}*
  
  ==================================
  exists D3, {D3 : eq N3 N4}
  
  Subgoal mult_func.2 is:
   exists D3, {D3 : eq z N4}
  
  mult_func.1>> cases H2.
  
  Subgoal mult_func.1:
  
  Vars: N9:o, M1:o, P1:o, N7:o, M:o, P:o, N5:o, N4:o, N3:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N7 : nat}*
  H6:{N3 : nat}*
  H7:{M : mult N5 N2 N7}*
  H8:{P : plus N2 N7 N3}*
  H9:{N5 : nat}
  H10:{N2 : nat}
  H11:{N9 : nat}
  H12:{N4 : nat}
  H13:{M1 : mult N5 N2 N9}
  H14:{P1 : plus N2 N9 N4}
  
  ==================================
  exists D3, {D3 : eq N3 N4}
  
  Subgoal mult_func.2 is:
   exists D3, {D3 : eq z N4}
  
  mult_func.1>> apply IH to H7 H13 with N1 = N5, N2 = N2, N3 = N7, N4 = N9, D1 = M, D2 = M1.
  
  Subgoal mult_func.1:
  
  Vars: D3:o, N9:o, M1:o, P1:o, N7:o, M:o, P:o, N5:o, N4:o, N3:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N7 : nat}*
  H6:{N3 : nat}*
  H7:{M : mult N5 N2 N7}*
  H8:{P : plus N2 N7 N3}*
  H9:{N5 : nat}
  H10:{N2 : nat}
  H11:{N9 : nat}
  H12:{N4 : nat}
  H13:{M1 : mult N5 N2 N9}
  H14:{P1 : plus N2 N9 N4}
  H15:{D3 : eq N7 N9}
  
  ==================================
  exists D3, {D3 : eq N3 N4}
  
  Subgoal mult_func.2 is:
   exists D3, {D3 : eq z N4}
  
  mult_func.1>> cases H15.
  
  Subgoal mult_func.1:
  
  Vars: N9:o, M1:o, P1:o, M:o, P:o, N5:o, N4:o, N3:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N9 : nat}*
  H6:{N3 : nat}*
  H7:{M : mult N5 N2 N9}*
  H8:{P : plus N2 N9 N3}*
  H9:{N5 : nat}
  H10:{N2 : nat}
  H11:{N9 : nat}
  H12:{N4 : nat}
  H13:{M1 : mult N5 N2 N9}
  H14:{P1 : plus N2 N9 N4}
  H16:{N9 : nat}
  
  ==================================
  exists D3, {D3 : eq N3 N4}
  
  Subgoal mult_func.2 is:
   exists D3, {D3 : eq z N4}
  
  mult_func.1>> apply plus_func2 to H8 H14 with N1 = N2, N2 = N9, N3 = N3, N4 = N4, D1 = P,
      D2 = P1.
  
  Subgoal mult_func.1:
  
  Vars: D:o, N9:o, M1:o, P1:o, M:o, P:o, N5:o, N4:o, N3:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N9 : nat}*
  H6:{N3 : nat}*
  H7:{M : mult N5 N2 N9}*
  H8:{P : plus N2 N9 N3}*
  H9:{N5 : nat}
  H10:{N2 : nat}
  H11:{N9 : nat}
  H12:{N4 : nat}
  H13:{M1 : mult N5 N2 N9}
  H14:{P1 : plus N2 N9 N4}
  H16:{N9 : nat}
  H17:{D : eq N3 N4}
  
  ==================================
  exists D3, {D3 : eq N3 N4}
  
  Subgoal mult_func.2 is:
   exists D3, {D3 : eq z N4}
  
  mult_func.1>> exists D.
  
  Subgoal mult_func.1:
  
  Vars: D:o, N9:o, M1:o, P1:o, M:o, P:o, N5:o, N4:o, N3:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H3:{N5 : nat}*
  H4:{N2 : nat}*
  H5:{N9 : nat}*
  H6:{N3 : nat}*
  H7:{M : mult N5 N2 N9}*
  H8:{P : plus N2 N9 N3}*
  H9:{N5 : nat}
  H10:{N2 : nat}
  H11:{N9 : nat}
  H12:{N4 : nat}
  H13:{M1 : mult N5 N2 N9}
  H14:{P1 : plus N2 N9 N4}
  H16:{N9 : nat}
  H17:{D : eq N3 N4}
  
  ==================================
  {D : eq N3 N4}
  
  Subgoal mult_func.2 is:
   exists D3, {D3 : eq z N4}
  
  mult_func.1>> search.
  
  Subgoal mult_func.2:
  
  Vars: D2:o, N4:o, N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H2:{D2 : mult z N2 N4}
  H3:{N2 : nat}*
  
  ==================================
  exists D3, {D3 : eq z N4}
  
  mult_func.2>> cases H2.
  
  Subgoal mult_func.2:
  
  Vars: N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H3:{N2 : nat}*
  H4:{N2 : nat}
  
  ==================================
  exists D3, {D3 : eq z z}
  
  mult_func.2>> exists refl z.
  
  Subgoal mult_func.2:
  
  Vars: N2:o
  IH:
      forall N1, forall N2, forall N3, forall N4, forall D1, forall D2,
        {D1 : mult N1 N2 N3}* =>
            {D2 : mult N1 N2 N4} => exists D3, {D3 : eq N3 N4}
  H3:{N2 : nat}*
  H4:{N2 : nat}
  
  ==================================
  {refl z : eq z z}
  
  mult_func.2>> search.
  Proof Completed!
  
  >> Goodbye!
