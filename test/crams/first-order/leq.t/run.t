  $ adelfa -i leq-properties.ath
  Welcome!
  >> Specification leq-properties.lf.
  
  >> Theorem plus-zero-id:
      forall  x1, {x1 : nat} => exists  D, {D : plus x1 z x1}.
  
  Subgoal plus-zero-id:
  
  
  ==================================
  forall x1, {x1 : nat} => exists D, {D : plus x1 z x1}
  
  plus-zero-id>> induction on 1.
  
  Subgoal plus-zero-id:
  
  IH:forall x1, {x1 : nat}* => exists D, {D : plus x1 z x1}
  
  ==================================
  forall x1, {x1 : nat}@ => exists D, {D : plus x1 z x1}
  
  plus-zero-id>> intros.
  
  Subgoal plus-zero-id:
  
  Vars: x1:o
  IH:forall x1, {x1 : nat}* => exists D, {D : plus x1 z x1}
  H1:{x1 : nat}@
  
  ==================================
  exists D, {D : plus x1 z x1}
  
  plus-zero-id>> cases H1.
  
  Subgoal plus-zero-id.1:
  
  Vars: x:o
  IH:forall x1, {x1 : nat}* => exists D, {D : plus x1 z x1}
  H2:{x : nat}*
  
  ==================================
  exists D, {D : plus (s x) z (s x)}
  
  Subgoal plus-zero-id.2 is:
   exists D, {D : plus z z z}
  
  plus-zero-id.1>> apply IH to H2.
  
  Subgoal plus-zero-id.1:
  
  Vars: D:o, x:o
  IH:forall x1, {x1 : nat}* => exists D, {D : plus x1 z x1}
  H2:{x : nat}*
  H3:{D : plus x z x}
  
  ==================================
  exists D, {D : plus (s x) z (s x)}
  
  Subgoal plus-zero-id.2 is:
   exists D, {D : plus z z z}
  
  plus-zero-id.1>> exists plus-s x z x D.
  
  Subgoal plus-zero-id.1:
  
  Vars: D:o, x:o
  IH:forall x1, {x1 : nat}* => exists D, {D : plus x1 z x1}
  H2:{x : nat}*
  H3:{D : plus x z x}
  
  ==================================
  {plus-s x z x D : plus (s x) z (s x)}
  
  Subgoal plus-zero-id.2 is:
   exists D, {D : plus z z z}
  
  plus-zero-id.1>> search.
  
  Subgoal plus-zero-id.2:
  
  IH:forall x1, {x1 : nat}* => exists D, {D : plus x1 z x1}
  
  ==================================
  exists D, {D : plus z z z}
  
  plus-zero-id.2>> exists plus-z z.
  
  Subgoal plus-zero-id.2:
  
  IH:forall x1, {x1 : nat}* => exists D, {D : plus x1 z x1}
  
  ==================================
  {plus-z z : plus z z z}
  
  plus-zero-id.2>> search.
  Proof Completed!
  
  >> Theorem plus-flip:
      forall  x1 x2 x3 D,
        {D : plus x1 x2 x3} => exists  D2, {D2 : plus x1 s x2 s x3}.
  
  Subgoal plus-flip:
  
  
  ==================================
  forall x1, forall x2, forall x3, forall D,
    {D : plus x1 x2 x3} => exists D2, {D2 : plus x1 (s x2) (s x3)}
  
  plus-flip>> induction on 1.
  
  Subgoal plus-flip:
  
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x1 (s x2) (s x3)}
  
  ==================================
  forall x1, forall x2, forall x3, forall D,
    {D : plus x1 x2 x3}@ => exists D2, {D2 : plus x1 (s x2) (s x3)}
  
  plus-flip>> intros.
  
  Subgoal plus-flip:
  
  Vars: D:o, x3:o, x2:o, x1:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x1 (s x2) (s x3)}
  H1:{D : plus x1 x2 x3}@
  
  ==================================
  exists D2, {D2 : plus x1 (s x2) (s x3)}
  
  plus-flip>> cases H1.
  
  Subgoal plus-flip.1:
  
  Vars: d:o, x4:o, x6:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x1 (s x2) (s x3)}
  H2:{x4 : nat}*
  H3:{x2 : nat}*
  H4:{x6 : nat}*
  H5:{d : plus x4 x2 x6}*
  
  ==================================
  exists D2, {D2 : plus (s x4) (s x2) (s (s x6))}
  
  Subgoal plus-flip.2 is:
   exists D2, {D2 : plus z (s x3) (s x3)}
  
  plus-flip.1>> apply IH to H5.
  
  Subgoal plus-flip.1:
  
  Vars: D2:o, d:o, x4:o, x6:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x1 (s x2) (s x3)}
  H2:{x4 : nat}*
  H3:{x2 : nat}*
  H4:{x6 : nat}*
  H5:{d : plus x4 x2 x6}*
  H6:{D2 : plus x4 (s x2) (s x6)}
  
  ==================================
  exists D2, {D2 : plus (s x4) (s x2) (s (s x6))}
  
  Subgoal plus-flip.2 is:
   exists D2, {D2 : plus z (s x3) (s x3)}
  
  plus-flip.1>> exists plus-s x4 s x2 s x6 D2.
  
  Subgoal plus-flip.1:
  
  Vars: D2:o, d:o, x4:o, x6:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x1 (s x2) (s x3)}
  H2:{x4 : nat}*
  H3:{x2 : nat}*
  H4:{x6 : nat}*
  H5:{d : plus x4 x2 x6}*
  H6:{D2 : plus x4 (s x2) (s x6)}
  
  ==================================
  {plus-s x4 (s x2) (s x6) D2 : plus (s x4) (s x2) (s (s x6))}
  
  Subgoal plus-flip.2 is:
   exists D2, {D2 : plus z (s x3) (s x3)}
  
  plus-flip.1>> search.
  
  Subgoal plus-flip.2:
  
  Vars: x3:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x1 (s x2) (s x3)}
  H2:{x3 : nat}*
  
  ==================================
  exists D2, {D2 : plus z (s x3) (s x3)}
  
  plus-flip.2>> exists plus-z s x3.
  
  Subgoal plus-flip.2:
  
  Vars: x3:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x1 (s x2) (s x3)}
  H2:{x3 : nat}*
  
  ==================================
  {plus-z (s x3) : plus z (s x3) (s x3)}
  
  plus-flip.2>> search.
  Proof Completed!
  
  >> Theorem plus-commutes:
      forall  x1 x2 x3 D,
        {D : plus x1 x2 x3} => exists  D2, {D2 : plus x2 x1 x3}.
  
  Subgoal plus-commutes:
  
  
  ==================================
  forall x1, forall x2, forall x3, forall D,
    {D : plus x1 x2 x3} => exists D2, {D2 : plus x2 x1 x3}
  
  plus-commutes>> induction on 1.
  
  Subgoal plus-commutes:
  
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  
  ==================================
  forall x1, forall x2, forall x3, forall D,
    {D : plus x1 x2 x3}@ => exists D2, {D2 : plus x2 x1 x3}
  
  plus-commutes>> intros.
  
  Subgoal plus-commutes:
  
  Vars: D:o, x3:o, x2:o, x1:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  H1:{D : plus x1 x2 x3}@
  
  ==================================
  exists D2, {D2 : plus x2 x1 x3}
  
  plus-commutes>> cases H1.
  
  Subgoal plus-commutes.1:
  
  Vars: d:o, x4:o, x6:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  H2:{x4 : nat}*
  H3:{x2 : nat}*
  H4:{x6 : nat}*
  H5:{d : plus x4 x2 x6}*
  
  ==================================
  exists D2, {D2 : plus x2 (s x4) (s x6)}
  
  Subgoal plus-commutes.2 is:
   exists D2, {D2 : plus x3 z x3}
  
  plus-commutes.1>> apply IH to H5.
  
  Subgoal plus-commutes.1:
  
  Vars: D2:o, d:o, x4:o, x6:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  H2:{x4 : nat}*
  H3:{x2 : nat}*
  H4:{x6 : nat}*
  H5:{d : plus x4 x2 x6}*
  H6:{D2 : plus x2 x4 x6}
  
  ==================================
  exists D2, {D2 : plus x2 (s x4) (s x6)}
  
  Subgoal plus-commutes.2 is:
   exists D2, {D2 : plus x3 z x3}
  
  plus-commutes.1>> apply plus-flip to H6.
  
  Subgoal plus-commutes.1:
  
  Vars: D1:o, D2:o, d:o, x4:o, x6:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  H2:{x4 : nat}*
  H3:{x2 : nat}*
  H4:{x6 : nat}*
  H5:{d : plus x4 x2 x6}*
  H6:{D2 : plus x2 x4 x6}
  H7:{D1 : plus x2 (s x4) (s x6)}
  
  ==================================
  exists D2, {D2 : plus x2 (s x4) (s x6)}
  
  Subgoal plus-commutes.2 is:
   exists D2, {D2 : plus x3 z x3}
  
  plus-commutes.1>> exists D1.
  
  Subgoal plus-commutes.1:
  
  Vars: D1:o, D2:o, d:o, x4:o, x6:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  H2:{x4 : nat}*
  H3:{x2 : nat}*
  H4:{x6 : nat}*
  H5:{d : plus x4 x2 x6}*
  H6:{D2 : plus x2 x4 x6}
  H7:{D1 : plus x2 (s x4) (s x6)}
  
  ==================================
  {D1 : plus x2 (s x4) (s x6)}
  
  Subgoal plus-commutes.2 is:
   exists D2, {D2 : plus x3 z x3}
  
  plus-commutes.1>> search.
  
  Subgoal plus-commutes.2:
  
  Vars: x3:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  H2:{x3 : nat}*
  
  ==================================
  exists D2, {D2 : plus x3 z x3}
  
  plus-commutes.2>> apply plus-zero-id to H2.
  
  Subgoal plus-commutes.2:
  
  Vars: D:o, x3:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  H2:{x3 : nat}*
  H3:{D : plus x3 z x3}
  
  ==================================
  exists D2, {D2 : plus x3 z x3}
  
  plus-commutes.2>> exists D.
  
  Subgoal plus-commutes.2:
  
  Vars: D:o, x3:o
  IH:
      forall x1, forall x2, forall x3, forall D,
        {D : plus x1 x2 x3}* => exists D2, {D2 : plus x2 x1 x3}
  H2:{x3 : nat}*
  H3:{D : plus x3 z x3}
  
  ==================================
  {D : plus x3 z x3}
  
  plus-commutes.2>> search.
  Proof Completed!
  
  >> Theorem leq-reflexive: forall  x, {x : nat} => exists  D, {D : leq x x}.
  
  Subgoal leq-reflexive:
  
  
  ==================================
  forall x, {x : nat} => exists D, {D : leq x x}
  
  leq-reflexive>> induction on 1.
  
  Subgoal leq-reflexive:
  
  IH:forall x, {x : nat}* => exists D, {D : leq x x}
  
  ==================================
  forall x, {x : nat}@ => exists D, {D : leq x x}
  
  leq-reflexive>> intros.
  
  Subgoal leq-reflexive:
  
  Vars: x:o
  IH:forall x, {x : nat}* => exists D, {D : leq x x}
  H1:{x : nat}@
  
  ==================================
  exists D, {D : leq x x}
  
  leq-reflexive>> cases H1.
  
  Subgoal leq-reflexive.1:
  
  Vars: x1:o
  IH:forall x, {x : nat}* => exists D, {D : leq x x}
  H2:{x1 : nat}*
  
  ==================================
  exists D, {D : leq (s x1) (s x1)}
  
  Subgoal leq-reflexive.2 is:
   exists D, {D : leq z z}
  
  leq-reflexive.1>> apply IH to H2.
  
  Subgoal leq-reflexive.1:
  
  Vars: D:o, x1:o
  IH:forall x, {x : nat}* => exists D, {D : leq x x}
  H2:{x1 : nat}*
  H3:{D : leq x1 x1}
  
  ==================================
  exists D, {D : leq (s x1) (s x1)}
  
  Subgoal leq-reflexive.2 is:
   exists D, {D : leq z z}
  
  leq-reflexive.1>> exists leq-s x1 x1 D.
  
  Subgoal leq-reflexive.1:
  
  Vars: D:o, x1:o
  IH:forall x, {x : nat}* => exists D, {D : leq x x}
  H2:{x1 : nat}*
  H3:{D : leq x1 x1}
  
  ==================================
  {leq-s x1 x1 D : leq (s x1) (s x1)}
  
  Subgoal leq-reflexive.2 is:
   exists D, {D : leq z z}
  
  leq-reflexive.1>> search.
  
  Subgoal leq-reflexive.2:
  
  IH:forall x, {x : nat}* => exists D, {D : leq x x}
  
  ==================================
  exists D, {D : leq z z}
  
  leq-reflexive.2>> exists leq-z z.
  
  Subgoal leq-reflexive.2:
  
  IH:forall x, {x : nat}* => exists D, {D : leq x x}
  
  ==================================
  {leq-z z : leq z z}
  
  leq-reflexive.2>> search.
  Proof Completed!
  
  >> Theorem leq-antisymmetric:
      forall  x1 x2 D1 D2,
        {D1 : leq x1 x2} => {D2 : leq x2 x1} => exists  E, {E : eq-nat x1 x2}.
  
  Subgoal leq-antisymmetric:
  
  
  ==================================
  forall x1, forall x2, forall D1, forall D2,
    {D1 : leq x1 x2} => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  
  leq-antisymmetric>> induction on 1.
  
  Subgoal leq-antisymmetric:
  
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  
  ==================================
  forall x1, forall x2, forall D1, forall D2,
    {D1 : leq x1 x2}@ => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  
  leq-antisymmetric>> intros.
  
  Subgoal leq-antisymmetric:
  
  Vars: D2:o, D1:o, x2:o, x1:o
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  H1:{D1 : leq x1 x2}@
  H2:{D2 : leq x2 x1}
  
  ==================================
  exists E, {E : eq-nat x1 x2}
  
  leq-antisymmetric>> cases H1.
  
  Subgoal leq-antisymmetric.1:
  
  Vars: d:o, x3:o, x4:o, D2:o
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  H2:{D2 : leq (s x4) (s x3)}
  H3:{x3 : nat}*
  H4:{x4 : nat}*
  H5:{d : leq x3 x4}*
  
  ==================================
  exists E, {E : eq-nat (s x3) (s x4)}
  
  Subgoal leq-antisymmetric.2 is:
   exists E, {E : eq-nat z x2}
  
  leq-antisymmetric.1>> cases H2.
  
  Subgoal leq-antisymmetric.1:
  
  Vars: d1:o, d:o, x3:o, x4:o
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  H3:{x3 : nat}*
  H4:{x4 : nat}*
  H5:{d : leq x3 x4}*
  H6:{x4 : nat}
  H7:{x3 : nat}
  H8:{d1 : leq x4 x3}
  
  ==================================
  exists E, {E : eq-nat (s x3) (s x4)}
  
  Subgoal leq-antisymmetric.2 is:
   exists E, {E : eq-nat z x2}
  
  leq-antisymmetric.1>> apply IH to H5 H8.
  
  Subgoal leq-antisymmetric.1:
  
  Vars: E:o, d1:o, d:o, x3:o, x4:o
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  H3:{x3 : nat}*
  H4:{x4 : nat}*
  H5:{d : leq x3 x4}*
  H6:{x4 : nat}
  H7:{x3 : nat}
  H8:{d1 : leq x4 x3}
  H9:{E : eq-nat x3 x4}
  
  ==================================
  exists E, {E : eq-nat (s x3) (s x4)}
  
  Subgoal leq-antisymmetric.2 is:
   exists E, {E : eq-nat z x2}
  
  leq-antisymmetric.1>> exists eq-nat-s x3 x4 E.
  
  Subgoal leq-antisymmetric.1:
  
  Vars: E:o, d1:o, d:o, x3:o, x4:o
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  H3:{x3 : nat}*
  H4:{x4 : nat}*
  H5:{d : leq x3 x4}*
  H6:{x4 : nat}
  H7:{x3 : nat}
  H8:{d1 : leq x4 x3}
  H9:{E : eq-nat x3 x4}
  
  ==================================
  {eq-nat-s x3 x4 E : eq-nat (s x3) (s x4)}
  
  Subgoal leq-antisymmetric.2 is:
   exists E, {E : eq-nat z x2}
  
  leq-antisymmetric.1>> search.
  
  Subgoal leq-antisymmetric.2:
  
  Vars: D2:o, x2:o
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  H2:{D2 : leq x2 z}
  H3:{x2 : nat}*
  
  ==================================
  exists E, {E : eq-nat z x2}
  
  leq-antisymmetric.2>> cases H2.
  
  Subgoal leq-antisymmetric.2:
  
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  H3:{z : nat}*
  H4:{z : nat}
  
  ==================================
  exists E, {E : eq-nat z z}
  
  leq-antisymmetric.2>> exists eq-nat-z.
  
  Subgoal leq-antisymmetric.2:
  
  IH:
      forall x1, forall x2, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x1} => exists E, {E : eq-nat x1 x2}
  H3:{z : nat}*
  H4:{z : nat}
  
  ==================================
  {eq-nat-z : eq-nat z z}
  
  leq-antisymmetric.2>> search.
  Proof Completed!
  
  >> Theorem leq-transitive:
      forall  x1 x2 x3 D1 D2,
        {D1 : leq x1 x2} => {D2 : leq x2 x3} => exists  E, {E : leq x1 x3}.
  
  Subgoal leq-transitive:
  
  
  ==================================
  forall x1, forall x2, forall x3, forall D1, forall D2,
    {D1 : leq x1 x2} => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  
  leq-transitive>> induction on 1.
  
  Subgoal leq-transitive:
  
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  
  ==================================
  forall x1, forall x2, forall x3, forall D1, forall D2,
    {D1 : leq x1 x2}@ => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  
  leq-transitive>> intros.
  
  Subgoal leq-transitive:
  
  Vars: D2:o, D1:o, x3:o, x2:o, x1:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H1:{D1 : leq x1 x2}@
  H2:{D2 : leq x2 x3}
  
  ==================================
  exists E, {E : leq x1 x3}
  
  leq-transitive>> cases H1.
  
  Subgoal leq-transitive.1:
  
  Vars: d:o, x4:o, x5:o, D2:o, x3:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H2:{D2 : leq (s x5) x3}
  H3:{x4 : nat}*
  H4:{x5 : nat}*
  H5:{d : leq x4 x5}*
  
  ==================================
  exists E, {E : leq (s x4) x3}
  
  Subgoal leq-transitive.2 is:
   exists E, {E : leq z x3}
  
  leq-transitive.1>> cases H2.
  
  Subgoal leq-transitive.1:
  
  Vars: d1:o, x7:o, d:o, x4:o, x5:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H3:{x4 : nat}*
  H4:{x5 : nat}*
  H5:{d : leq x4 x5}*
  H6:{x5 : nat}
  H7:{x7 : nat}
  H8:{d1 : leq x5 x7}
  
  ==================================
  exists E, {E : leq (s x4) (s x7)}
  
  Subgoal leq-transitive.2 is:
   exists E, {E : leq z x3}
  
  leq-transitive.1>> apply IH to H5 H8.
  
  Subgoal leq-transitive.1:
  
  Vars: E:o, d1:o, x7:o, d:o, x4:o, x5:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H3:{x4 : nat}*
  H4:{x5 : nat}*
  H5:{d : leq x4 x5}*
  H6:{x5 : nat}
  H7:{x7 : nat}
  H8:{d1 : leq x5 x7}
  H9:{E : leq x4 x7}
  
  ==================================
  exists E, {E : leq (s x4) (s x7)}
  
  Subgoal leq-transitive.2 is:
   exists E, {E : leq z x3}
  
  leq-transitive.1>> exists leq-s x4 x7 E.
  
  Subgoal leq-transitive.1:
  
  Vars: E:o, d1:o, x7:o, d:o, x4:o, x5:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H3:{x4 : nat}*
  H4:{x5 : nat}*
  H5:{d : leq x4 x5}*
  H6:{x5 : nat}
  H7:{x7 : nat}
  H8:{d1 : leq x5 x7}
  H9:{E : leq x4 x7}
  
  ==================================
  {leq-s x4 x7 E : leq (s x4) (s x7)}
  
  Subgoal leq-transitive.2 is:
   exists E, {E : leq z x3}
  
  leq-transitive.1>> search.
  
  Subgoal leq-transitive.2:
  
  Vars: D2:o, x3:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H2:{D2 : leq x2 x3}
  H3:{x2 : nat}*
  
  ==================================
  exists E, {E : leq z x3}
  
  leq-transitive.2>> cases H2.
  
  Subgoal leq-transitive.2.1:
  
  Vars: d:o, x4:o, x5:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H3:{s x4 : nat}*
  H4:{x4 : nat}
  H5:{x5 : nat}
  H6:{d : leq x4 x5}
  
  ==================================
  exists E, {E : leq z (s x5)}
  
  Subgoal leq-transitive.2.2 is:
   exists E, {E : leq z x3}
  
  leq-transitive.2.1>> exists leq-z s x5.
  
  Subgoal leq-transitive.2.1:
  
  Vars: d:o, x4:o, x5:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H3:{s x4 : nat}*
  H4:{x4 : nat}
  H5:{x5 : nat}
  H6:{d : leq x4 x5}
  
  ==================================
  {leq-z (s x5) : leq z (s x5)}
  
  Subgoal leq-transitive.2.2 is:
   exists E, {E : leq z x3}
  
  leq-transitive.2.1>> search.
  
  Subgoal leq-transitive.2.2:
  
  Vars: x3:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H3:{z : nat}*
  H4:{x3 : nat}
  
  ==================================
  exists E, {E : leq z x3}
  
  leq-transitive.2.2>> exists leq-z x3.
  
  Subgoal leq-transitive.2.2:
  
  Vars: x3:o
  IH:
      forall x1, forall x2, forall x3, forall D1, forall D2,
        {D1 : leq x1 x2}* => {D2 : leq x2 x3} => exists E, {E : leq x1 x3}
  H3:{z : nat}*
  H4:{x3 : nat}
  
  ==================================
  {leq-z x3 : leq z x3}
  
  leq-transitive.2.2>> search.
  Proof Completed!
  
  >> Theorem leq-monotonic-plus-r:
      forall  x1 x2 x3 x12 x13 D1 D2 D3,
        {D2 : plus x1 x2 x12} =>
          {D1 : leq x2 x3} =>
            {D3 : plus x1 x3 x13} => exists  E, {E : leq x12 x13}.
  
  Subgoal leq-monotonic-plus-r:
  
  
  ==================================
  forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
    forall D2, forall D3,
    {D2 : plus x1 x2 x12} =>
        {D1 : leq x2 x3} =>
            {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r>> induction on 1.
  
  Subgoal leq-monotonic-plus-r:
  
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  
  ==================================
  forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
    forall D2, forall D3,
    {D2 : plus x1 x2 x12}@ =>
        {D1 : leq x2 x3} =>
            {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r>> intros.
  
  Subgoal leq-monotonic-plus-r:
  
  Vars: D3:o, D2:o, D1:o, x13:o, x12:o, x3:o, x2:o, x1:o
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  H1:{D2 : plus x1 x2 x12}@
  H2:{D1 : leq x2 x3}
  H3:{D3 : plus x1 x3 x13}
  
  ==================================
  exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r>> cases H1.
  
  Subgoal leq-monotonic-plus-r.1:
  
  Vars: d:o, x4:o, x6:o, D3:o, D1:o, x13:o, x3:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  H2:{D1 : leq x2 x3}
  H3:{D3 : plus (s x4) x3 x13}
  H4:{x4 : nat}*
  H5:{x2 : nat}*
  H6:{x6 : nat}*
  H7:{d : plus x4 x2 x6}*
  
  ==================================
  exists E, {E : leq (s x6) x13}
  
  Subgoal leq-monotonic-plus-r.2 is:
   exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r.1>> cases H3.
  
  Subgoal leq-monotonic-plus-r.1:
  
  Vars: d1:o, x8:o, d:o, x4:o, x6:o, D1:o, x3:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  H2:{D1 : leq x2 x3}
  H4:{x4 : nat}*
  H5:{x2 : nat}*
  H6:{x6 : nat}*
  H7:{d : plus x4 x2 x6}*
  H8:{x4 : nat}
  H9:{x3 : nat}
  H10:{x8 : nat}
  H11:{d1 : plus x4 x3 x8}
  
  ==================================
  exists E, {E : leq (s x6) (s x8)}
  
  Subgoal leq-monotonic-plus-r.2 is:
   exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r.1>> apply IH to H7 H2 H11.
  
  Subgoal leq-monotonic-plus-r.1:
  
  Vars: E:o, d1:o, x8:o, d:o, x4:o, x6:o, D1:o, x3:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  H2:{D1 : leq x2 x3}
  H4:{x4 : nat}*
  H5:{x2 : nat}*
  H6:{x6 : nat}*
  H7:{d : plus x4 x2 x6}*
  H8:{x4 : nat}
  H9:{x3 : nat}
  H10:{x8 : nat}
  H11:{d1 : plus x4 x3 x8}
  H12:{E : leq x6 x8}
  
  ==================================
  exists E, {E : leq (s x6) (s x8)}
  
  Subgoal leq-monotonic-plus-r.2 is:
   exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r.1>> exists leq-s x6 x8 E.
  
  Subgoal leq-monotonic-plus-r.1:
  
  Vars: E:o, d1:o, x8:o, d:o, x4:o, x6:o, D1:o, x3:o, x2:o
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  H2:{D1 : leq x2 x3}
  H4:{x4 : nat}*
  H5:{x2 : nat}*
  H6:{x6 : nat}*
  H7:{d : plus x4 x2 x6}*
  H8:{x4 : nat}
  H9:{x3 : nat}
  H10:{x8 : nat}
  H11:{d1 : plus x4 x3 x8}
  H12:{E : leq x6 x8}
  
  ==================================
  {leq-s x6 x8 E : leq (s x6) (s x8)}
  
  Subgoal leq-monotonic-plus-r.2 is:
   exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r.1>> search.
  
  Subgoal leq-monotonic-plus-r.2:
  
  Vars: D3:o, D1:o, x13:o, x12:o, x3:o
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  H2:{D1 : leq x12 x3}
  H3:{D3 : plus z x3 x13}
  H4:{x12 : nat}*
  
  ==================================
  exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r.2>> cases H3.
  
  Subgoal leq-monotonic-plus-r.2:
  
  Vars: D1:o, x13:o, x12:o
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  H2:{D1 : leq x12 x13}
  H4:{x12 : nat}*
  H5:{x13 : nat}
  
  ==================================
  exists E, {E : leq x12 x13}
  
  leq-monotonic-plus-r.2>> exists D1.
  
  Subgoal leq-monotonic-plus-r.2:
  
  Vars: D1:o, x13:o, x12:o
  IH:
      forall x1, forall x2, forall x3, forall x12, forall x13, forall D1,
        forall D2, forall D3,
        {D2 : plus x1 x2 x12}* =>
            {D1 : leq x2 x3} =>
                {D3 : plus x1 x3 x13} => exists E, {E : leq x12 x13}
  H2:{D1 : leq x12 x13}
  H4:{x12 : nat}*
  H5:{x13 : nat}
  
  ==================================
  {D1 : leq x12 x13}
  
  leq-monotonic-plus-r.2>> search.
  Proof Completed!
  
  >> Theorem leq-monotonic-plus-l:
      forall  x1 x2 x3 x13 x23 D1 D2 D3,
        {D1 : leq x1 x2} =>
          {D2 : plus x1 x3 x13} =>
            {D3 : plus x2 x3 x23} => exists  E, {E : leq x13 x23}.
  
  Subgoal leq-monotonic-plus-l:
  
  
  ==================================
  forall x1, forall x2, forall x3, forall x13, forall x23, forall D1,
    forall D2, forall D3,
    {D1 : leq x1 x2} =>
        {D2 : plus x1 x3 x13} =>
            {D3 : plus x2 x3 x23} => exists E, {E : leq x13 x23}
  
  leq-monotonic-plus-l>> intros.
  
  Subgoal leq-monotonic-plus-l:
  
  Vars: D3:o, D2:o, D1:o, x23:o, x13:o, x3:o, x2:o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : plus x1 x3 x13}
  H3:{D3 : plus x2 x3 x23}
  
  ==================================
  exists E, {E : leq x13 x23}
  
  leq-monotonic-plus-l>> apply plus-commutes to H2.
  
  Subgoal leq-monotonic-plus-l:
  
  Vars: D4:o, D3:o, D2:o, D1:o, x23:o, x13:o, x3:o, x2:o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : plus x1 x3 x13}
  H3:{D3 : plus x2 x3 x23}
  H4:{D4 : plus x3 x1 x13}
  
  ==================================
  exists E, {E : leq x13 x23}
  
  leq-monotonic-plus-l>> apply plus-commutes to H3.
  
  Subgoal leq-monotonic-plus-l:
  
  Vars: D5:o, D4:o, D3:o, D2:o, D1:o, x23:o, x13:o, x3:o, x2:o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : plus x1 x3 x13}
  H3:{D3 : plus x2 x3 x23}
  H4:{D4 : plus x3 x1 x13}
  H5:{D5 : plus x3 x2 x23}
  
  ==================================
  exists E, {E : leq x13 x23}
  
  leq-monotonic-plus-l>> apply leq-monotonic-plus-r to H4 H1 H5.
  
  Subgoal leq-monotonic-plus-l:
  
  Vars: E:o, D5:o, D4:o, D3:o, D2:o, D1:o, x23:o, x13:o, x3:o, x2:o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : plus x1 x3 x13}
  H3:{D3 : plus x2 x3 x23}
  H4:{D4 : plus x3 x1 x13}
  H5:{D5 : plus x3 x2 x23}
  H6:{E : leq x13 x23}
  
  ==================================
  exists E, {E : leq x13 x23}
  
  leq-monotonic-plus-l>> exists E.
  
  Subgoal leq-monotonic-plus-l:
  
  Vars: E:o, D5:o, D4:o, D3:o, D2:o, D1:o, x23:o, x13:o, x3:o, x2:o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : plus x1 x3 x13}
  H3:{D3 : plus x2 x3 x23}
  H4:{D4 : plus x3 x1 x13}
  H5:{D5 : plus x3 x2 x23}
  H6:{E : leq x13 x23}
  
  ==================================
  {E : leq x13 x23}
  
  leq-monotonic-plus-l>> search.
  Proof Completed!
  
  >> Theorem leq-monotonic-plus:
      forall  x1 x2 x3 x4 x13 x23 x24 D1 D2 D3 D4 D5,
        {D1 : leq x1 x2} =>
          {D2 : leq x3 x4} =>
            {D3 : plus x1 x3 x13} =>
              {D4 : plus x2 x4 x24} =>
                {D5 : plus x2 x3 x23} => exists  E, {E : leq x13 x24}.
  
  Subgoal leq-monotonic-plus:
  
  
  ==================================
  forall x1, forall x2, forall x3, forall x4, forall x13, forall x23,
    forall x24, forall D1, forall D2, forall D3, forall D4, forall D5,
    {D1 : leq x1 x2} =>
        {D2 : leq x3 x4} =>
            {D3 : plus x1 x3 x13} =>
                {D4 : plus x2 x4 x24} =>
                    {D5 : plus x2 x3 x23} => exists E, {E : leq x13 x24}
  
  leq-monotonic-plus>> intros.
  
  Subgoal leq-monotonic-plus:
  
  Vars: D5:o, D4:o, D3:o, D2:o, D1:o, x24:o, x23:o, x13:o, x4:o, x3:o, x2:o, x1
          :o
  H1:{D1 : leq x1 x2}
  H2:{D2 : leq x3 x4}
  H3:{D3 : plus x1 x3 x13}
  H4:{D4 : plus x2 x4 x24}
  H5:{D5 : plus x2 x3 x23}
  
  ==================================
  exists E, {E : leq x13 x24}
  
  leq-monotonic-plus>> apply leq-monotonic-plus-l to H1 H3 H5.
  
  Subgoal leq-monotonic-plus:
  
  Vars: E:o, D5:o, D4:o, D3:o, D2:o, D1:o, x24:o, x23:o, x13:o, x4:o, x3:o, x2:
          o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : leq x3 x4}
  H3:{D3 : plus x1 x3 x13}
  H4:{D4 : plus x2 x4 x24}
  H5:{D5 : plus x2 x3 x23}
  H6:{E : leq x13 x23}
  
  ==================================
  exists E, {E : leq x13 x24}
  
  leq-monotonic-plus>> apply leq-monotonic-plus-r to H5 H2 H4.
  
  Subgoal leq-monotonic-plus:
  
  Vars: E1:o, E:o, D5:o, D4:o, D3:o, D2:o, D1:o, x24:o, x23:o, x13:o, x4:o, x3:
          o, x2:o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : leq x3 x4}
  H3:{D3 : plus x1 x3 x13}
  H4:{D4 : plus x2 x4 x24}
  H5:{D5 : plus x2 x3 x23}
  H6:{E : leq x13 x23}
  H7:{E1 : leq x23 x24}
  
  ==================================
  exists E, {E : leq x13 x24}
  
  leq-monotonic-plus>> apply leq-transitive to H6 H7.
  
  Subgoal leq-monotonic-plus:
  
  Vars: E2:o, E1:o, E:o, D5:o, D4:o, D3:o, D2:o, D1:o, x24:o, x23:o, x13:o, x4:
          o, x3:o, x2:o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : leq x3 x4}
  H3:{D3 : plus x1 x3 x13}
  H4:{D4 : plus x2 x4 x24}
  H5:{D5 : plus x2 x3 x23}
  H6:{E : leq x13 x23}
  H7:{E1 : leq x23 x24}
  H8:{E2 : leq x13 x24}
  
  ==================================
  exists E, {E : leq x13 x24}
  
  leq-monotonic-plus>> exists E2.
  
  Subgoal leq-monotonic-plus:
  
  Vars: E2:o, E1:o, E:o, D5:o, D4:o, D3:o, D2:o, D1:o, x24:o, x23:o, x13:o, x4:
          o, x3:o, x2:o, x1:o
  H1:{D1 : leq x1 x2}
  H2:{D2 : leq x3 x4}
  H3:{D3 : plus x1 x3 x13}
  H4:{D4 : plus x2 x4 x24}
  H5:{D5 : plus x2 x3 x23}
  H6:{E : leq x13 x23}
  H7:{E1 : leq x23 x24}
  H8:{E2 : leq x13 x24}
  
  ==================================
  {E2 : leq x13 x24}
  
  leq-monotonic-plus>> search.
  Proof Completed!
  
  >> Goodbye!
