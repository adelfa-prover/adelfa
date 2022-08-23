  $ adelfa -i map.ath
  Welcome!
  >> Specification map.lf.
  
  >> Theorem map-eq:
      forall  L1 L2 L3 D1 D2 f,
        {D1 : map f L1 L2} =>
          {D2 : map f L1 L3} => exists  E, {E : eq-list L2 L3}.
  
  Subgoal map-eq:
  
  
  ==================================
  forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
    {D1 : map f L1 L2} => {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  
  map-eq>> induction on 1.
  
  Subgoal map-eq:
  
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  
  ==================================
  forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
    {D1 : map f L1 L2}@ => {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  
  map-eq>> intros.
  
  Subgoal map-eq:
  
  Vars: f:(o) -> o, D2:o, D1:o, L3:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H1:{D1 : map f L1 L2}@
  H2:{D2 : map f L1 L3}
  
  ==================================
  exists E, {E : eq-list L2 L3}
  
  map-eq>> cases H1.
  
  Subgoal map-eq.1:
  
  Vars: d:o, l1:o, f1:(o) -> o, e:o, l2:o, D2:o, L3:o
  Nominals: n:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H2:{D2 : map ([x]f1 x) (cons e l1) L3}
  H3:{n:nat |- f1 n : nat}*
  H4:{l1 : list}*
  H5:{l2 : list}*
  H6:{d : map ([x]f1 x) l1 l2}*
  H7:{e : nat}*
  
  ==================================
  exists E, {E : eq-list (cons (f1 e) l2) L3}
  
  Subgoal map-eq.2 is:
   exists E, {E : eq-list nil L3}
  
  map-eq.1>> cases H2.
  
  Subgoal map-eq.1:
  
  Vars: D3:o, L4:o, d:o, l1:o, f1:(o) -> o, e:o, l2:o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H3:{n:nat |- f1 n : nat}*
  H4:{l1 : list}*
  H5:{l2 : list}*
  H6:{d : map ([x]f1 x) l1 l2}*
  H7:{e : nat}*
  H8:{n1:nat |- f1 n1 : nat}
  H9:{l1 : list}
  H10:{L4 : list}
  H11:{D3 : map ([x]f1 x) l1 L4}
  H12:{e : nat}
  
  ==================================
  exists E, {E : eq-list (cons (f1 e) l2) (cons (f1 e) L4)}
  
  Subgoal map-eq.2 is:
   exists E, {E : eq-list nil L3}
  
  map-eq.1>> inst H3 with n = e.
  
  Subgoal map-eq.1:
  
  Vars: D3:o, L4:o, d:o, l1:o, f1:(o) -> o, e:o, l2:o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H3:{n:nat |- f1 n : nat}*
  H4:{l1 : list}*
  H5:{l2 : list}*
  H6:{d : map ([x]f1 x) l1 l2}*
  H7:{e : nat}*
  H8:{n1:nat |- f1 n1 : nat}
  H9:{l1 : list}
  H10:{L4 : list}
  H11:{D3 : map ([x]f1 x) l1 L4}
  H12:{e : nat}
  H13:{f1 e : nat}
  
  ==================================
  exists E, {E : eq-list (cons (f1 e) l2) (cons (f1 e) L4)}
  
  Subgoal map-eq.2 is:
   exists E, {E : eq-list nil L3}
  
  map-eq.1>> apply IH to H6 H11.
  
  Subgoal map-eq.1:
  
  Vars: E:(o) -> (o) -> o, D3:o, L4:o, d:o, l1:o, f1:(o) -> o, e:o, l2:o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H3:{n:nat |- f1 n : nat}*
  H4:{l1 : list}*
  H5:{l2 : list}*
  H6:{d : map ([x]f1 x) l1 l2}*
  H7:{e : nat}*
  H8:{n1:nat |- f1 n1 : nat}
  H9:{l1 : list}
  H10:{L4 : list}
  H11:{D3 : map ([x]f1 x) l1 L4}
  H12:{e : nat}
  H13:{f1 e : nat}
  H14:{E n1 n : eq-list l2 L4}
  
  ==================================
  exists E, {E : eq-list (cons (f1 e) l2) (cons (f1 e) L4)}
  
  Subgoal map-eq.2 is:
   exists E, {E : eq-list nil L3}
  
  map-eq.1>> exists eq-list-cons l2 L4 f1 e E n1 n.
  
  Subgoal map-eq.1:
  
  Vars: E:(o) -> (o) -> o, D3:o, L4:o, d:o, l1:o, f1:(o) -> o, e:o, l2:o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H3:{n:nat |- f1 n : nat}*
  H4:{l1 : list}*
  H5:{l2 : list}*
  H6:{d : map ([x]f1 x) l1 l2}*
  H7:{e : nat}*
  H8:{n1:nat |- f1 n1 : nat}
  H9:{l1 : list}
  H10:{L4 : list}
  H11:{D3 : map ([x]f1 x) l1 L4}
  H12:{e : nat}
  H13:{f1 e : nat}
  H14:{E n1 n : eq-list l2 L4}
  
  ==================================
  {eq-list-cons l2 L4 (f1 e) (E n1 n) :
    eq-list (cons (f1 e) l2) (cons (f1 e) L4)}
  
  Subgoal map-eq.2 is:
   exists E, {E : eq-list nil L3}
  
  map-eq.1>> search.
  
  Subgoal map-eq.2:
  
  Vars: f1:(o) -> o, D2:o, L3:o
  Nominals: n:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H2:{D2 : map ([x]f1 x) nil L3}
  H3:{n:nat |- f1 n : nat}*
  
  ==================================
  exists E, {E : eq-list nil L3}
  
  map-eq.2>> cases H2.
  
  Subgoal map-eq.2:
  
  Vars: f1:(o) -> o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H3:{n:nat |- f1 n : nat}*
  H4:{n1:nat |- f1 n1 : nat}
  
  ==================================
  exists E, {E : eq-list nil nil}
  
  map-eq.2>> exists eq-list-nil.
  
  Subgoal map-eq.2:
  
  Vars: f1:(o) -> o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L3, forall D1, forall D2, forall f,
        {D1 : map f L1 L2}* =>
            {D2 : map f L1 L3} => exists E, {E : eq-list L2 L3}
  H3:{n:nat |- f1 n : nat}*
  H4:{n1:nat |- f1 n1 : nat}
  
  ==================================
  {eq-list-nil : eq-list nil nil}
  
  map-eq.2>> search.
  Proof Completed!
  
  >> Theorem map-distrib-append:
      forall  L1 L2 L12 f FL12 FL1 FL2 D1 D2 D3 D4 D5 FL12',
        {D1 : append L1 L2 L12} =>
          {D2 : map f L12 FL12} =>
            {D3 : map f L1 FL1} =>
              {D4 : map f L2 FL2} =>
                {D5 : append FL1 FL2 FL12'} =>
                  exists  E, {E : eq-list FL12 FL12'}.
  
  Subgoal map-distrib-append:
  
  
  ==================================
  forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
    forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
    forall FL12',
    {D1 : append L1 L2 L12} =>
        {D2 : map f L12 FL12} =>
            {D3 : map f L1 FL1} =>
                {D4 : map f L2 FL2} =>
                    {D5 : append FL1 FL2 FL12'} =>
                        exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append>> induction on 1.
  
  Subgoal map-distrib-append:
  
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  
  ==================================
  forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
    forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
    forall FL12',
    {D1 : append L1 L2 L12}@ =>
        {D2 : map f L12 FL12} =>
            {D3 : map f L1 FL1} =>
                {D4 : map f L2 FL2} =>
                    {D5 : append FL1 FL2 FL12'} =>
                        exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append>> intros.
  
  Subgoal map-distrib-append:
  
  Vars: FL12':o, D5:o, D4:o, D3:o, D2:o, D1:o, FL2:o, FL1:o, FL12:o, f:
          (o) -> o, L12:o, L2:o, L1:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H1:{D1 : append L1 L2 L12}@
  H2:{D2 : map f L12 FL12}
  H3:{D3 : map f L1 FL1}
  H4:{D4 : map f L2 FL2}
  H5:{D5 : append FL1 FL2 FL12'}
  
  ==================================
  exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append>> cases H1.
  
  Subgoal map-distrib-append.1:
  
  Vars: d:o, l1:o, x:o, l3:o, FL12':o, D5:o, D4:o, D3:o, D2:o, FL2:o, FL1:o,
          FL12:o, f:(o) -> o, L2:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H2:{D2 : map f (cons x l3) FL12}
  H3:{D3 : map f (cons x l1) FL1}
  H4:{D4 : map f L2 FL2}
  H5:{D5 : append FL1 FL2 FL12'}
  H6:{l1 : list}*
  H7:{L2 : list}*
  H8:{l3 : list}*
  H9:{x : nat}*
  H10:{d : append l1 L2 l3}*
  
  ==================================
  exists E, {E : eq-list FL12 FL12'}
  
  Subgoal map-distrib-append.2 is:
   exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.1>> cases H2.
  
  Subgoal map-distrib-append.1:
  
  Vars: d1:o, f1:(o) -> o, l4:o, d:o, l1:o, x:o, l3:o, FL12':o, D5:o, D4:o, D3:
          o, FL2:o, FL1:o, L2:o
  Nominals: n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H3:{D3 : map ([x]f1 x) (cons x l1) FL1}
  H4:{D4 : map ([x]f1 x) L2 FL2}
  H5:{D5 : append FL1 FL2 FL12'}
  H6:{l1 : list}*
  H7:{L2 : list}*
  H8:{l3 : list}*
  H9:{x : nat}*
  H10:{d : append l1 L2 l3}*
  H11:{n:nat |- f1 n : nat}
  H12:{l3 : list}
  H13:{l4 : list}
  H14:{d1 : map ([x]f1 x) l3 l4}
  H15:{x : nat}
  
  ==================================
  exists E, {E : eq-list (cons (f1 x) l4) FL12'}
  
  Subgoal map-distrib-append.2 is:
   exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.1>> cases H3.
  
  Subgoal map-distrib-append.1:
  
  Vars: D6:o, FL3:o, d1:o, f1:(o) -> o, l4:o, d:o, l1:o, x:o, l3:o, FL12':o, D5
          :o, D4:o, FL2:o, L2:o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H4:{D4 : map ([x]f1 x) L2 FL2}
  H5:{D5 : append (cons (f1 x) FL3) FL2 FL12'}
  H6:{l1 : list}*
  H7:{L2 : list}*
  H8:{l3 : list}*
  H9:{x : nat}*
  H10:{d : append l1 L2 l3}*
  H11:{n:nat |- f1 n : nat}
  H12:{l3 : list}
  H13:{l4 : list}
  H14:{d1 : map ([x]f1 x) l3 l4}
  H15:{x : nat}
  H16:{n1:nat |- f1 n1 : nat}
  H17:{l1 : list}
  H18:{FL3 : list}
  H19:{D6 : map ([x]f1 x) l1 FL3}
  H20:{x : nat}
  
  ==================================
  exists E, {E : eq-list (cons (f1 x) l4) FL12'}
  
  Subgoal map-distrib-append.2 is:
   exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.1>> cases H5.
  
  Subgoal map-distrib-append.1:
  
  Vars: D7:o, FL12'1:o, D6:o, FL3:o, d1:o, f1:(o) -> o, l4:o, d:o, l1:o, x:o,
          l3:o, D4:o, FL2:o, L2:o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H4:{D4 : map ([x]f1 x) L2 FL2}
  H6:{l1 : list}*
  H7:{L2 : list}*
  H8:{l3 : list}*
  H9:{x : nat}*
  H10:{d : append l1 L2 l3}*
  H11:{n:nat |- f1 n : nat}
  H12:{l3 : list}
  H13:{l4 : list}
  H14:{d1 : map ([x]f1 x) l3 l4}
  H15:{x : nat}
  H16:{n1:nat |- f1 n1 : nat}
  H17:{l1 : list}
  H18:{FL3 : list}
  H19:{D6 : map ([x]f1 x) l1 FL3}
  H20:{x : nat}
  H21:{FL3 : list}
  H22:{FL2 : list}
  H23:{FL12'1 : list}
  H24:{f1 x : nat}
  H25:{D7 : append FL3 FL2 FL12'1}
  
  ==================================
  exists E, {E : eq-list (cons (f1 x) l4) (cons (f1 x) FL12'1)}
  
  Subgoal map-distrib-append.2 is:
   exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.1>> apply IH to H10 H14 H19 H4 H25.
  
  Subgoal map-distrib-append.1:
  
  Vars: E:(o) -> (o) -> o, D7:o, FL12'1:o, D6:o, FL3:o, d1:o, f1:(o) -> o, l4:
          o, d:o, l1:o, x:o, l3:o, D4:o, FL2:o, L2:o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H4:{D4 : map ([x]f1 x) L2 FL2}
  H6:{l1 : list}*
  H7:{L2 : list}*
  H8:{l3 : list}*
  H9:{x : nat}*
  H10:{d : append l1 L2 l3}*
  H11:{n:nat |- f1 n : nat}
  H12:{l3 : list}
  H13:{l4 : list}
  H14:{d1 : map ([x]f1 x) l3 l4}
  H15:{x : nat}
  H16:{n1:nat |- f1 n1 : nat}
  H17:{l1 : list}
  H18:{FL3 : list}
  H19:{D6 : map ([x]f1 x) l1 FL3}
  H20:{x : nat}
  H21:{FL3 : list}
  H22:{FL2 : list}
  H23:{FL12'1 : list}
  H24:{f1 x : nat}
  H25:{D7 : append FL3 FL2 FL12'1}
  H26:{E n1 n : eq-list l4 FL12'1}
  
  ==================================
  exists E, {E : eq-list (cons (f1 x) l4) (cons (f1 x) FL12'1)}
  
  Subgoal map-distrib-append.2 is:
   exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.1>> exists eq-list-cons l4 FL12'1 f1 x E n1 n.
  
  Subgoal map-distrib-append.1:
  
  Vars: E:(o) -> (o) -> o, D7:o, FL12'1:o, D6:o, FL3:o, d1:o, f1:(o) -> o, l4:
          o, d:o, l1:o, x:o, l3:o, D4:o, FL2:o, L2:o
  Nominals: n1:o, n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H4:{D4 : map ([x]f1 x) L2 FL2}
  H6:{l1 : list}*
  H7:{L2 : list}*
  H8:{l3 : list}*
  H9:{x : nat}*
  H10:{d : append l1 L2 l3}*
  H11:{n:nat |- f1 n : nat}
  H12:{l3 : list}
  H13:{l4 : list}
  H14:{d1 : map ([x]f1 x) l3 l4}
  H15:{x : nat}
  H16:{n1:nat |- f1 n1 : nat}
  H17:{l1 : list}
  H18:{FL3 : list}
  H19:{D6 : map ([x]f1 x) l1 FL3}
  H20:{x : nat}
  H21:{FL3 : list}
  H22:{FL2 : list}
  H23:{FL12'1 : list}
  H24:{f1 x : nat}
  H25:{D7 : append FL3 FL2 FL12'1}
  H26:{E n1 n : eq-list l4 FL12'1}
  
  ==================================
  {eq-list-cons l4 FL12'1 (f1 x) (E n1 n) :
    eq-list (cons (f1 x) l4) (cons (f1 x) FL12'1)}
  
  Subgoal map-distrib-append.2 is:
   exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.1>> search.
  
  Subgoal map-distrib-append.2:
  
  Vars: FL12':o, D5:o, D4:o, D3:o, D2:o, FL2:o, FL1:o, FL12:o, f:(o) -> o, L12:
          o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H2:{D2 : map f L12 FL12}
  H3:{D3 : map f nil FL1}
  H4:{D4 : map f L12 FL2}
  H5:{D5 : append FL1 FL2 FL12'}
  H6:{L12 : list}*
  
  ==================================
  exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.2>> cases H3.
  
  Subgoal map-distrib-append.2:
  
  Vars: f1:(o) -> o, FL12':o, D5:o, D4:o, D2:o, FL2:o, FL12:o, L12:o
  Nominals: n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H2:{D2 : map ([x]f1 x) L12 FL12}
  H4:{D4 : map ([x]f1 x) L12 FL2}
  H5:{D5 : append nil FL2 FL12'}
  H6:{L12 : list}*
  H7:{n:nat |- f1 n : nat}
  
  ==================================
  exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.2>> cases H5.
  
  Subgoal map-distrib-append.2:
  
  Vars: f1:(o) -> o, FL12':o, D4:o, D2:o, FL12:o, L12:o
  Nominals: n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H2:{D2 : map ([x]f1 x) L12 FL12}
  H4:{D4 : map ([x]f1 x) L12 FL12'}
  H6:{L12 : list}*
  H7:{n:nat |- f1 n : nat}
  H8:{FL12' : list}
  
  ==================================
  exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.2>> apply map-eq to H2 H4.
  
  Subgoal map-distrib-append.2:
  
  Vars: E:(o) -> o, f1:(o) -> o, FL12':o, D4:o, D2:o, FL12:o, L12:o
  Nominals: n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H2:{D2 : map ([x]f1 x) L12 FL12}
  H4:{D4 : map ([x]f1 x) L12 FL12'}
  H6:{L12 : list}*
  H7:{n:nat |- f1 n : nat}
  H8:{FL12' : list}
  H9:{E n : eq-list FL12 FL12'}
  
  ==================================
  exists E, {E : eq-list FL12 FL12'}
  
  map-distrib-append.2>> exists E n.
  
  Subgoal map-distrib-append.2:
  
  Vars: E:(o) -> o, f1:(o) -> o, FL12':o, D4:o, D2:o, FL12:o, L12:o
  Nominals: n:o
  IH:
      forall L1, forall L2, forall L12, forall f, forall FL12, forall FL1,
        forall FL2, forall D1, forall D2, forall D3, forall D4, forall D5,
        forall FL12',
        {D1 : append L1 L2 L12}* =>
            {D2 : map f L12 FL12} =>
                {D3 : map f L1 FL1} =>
                    {D4 : map f L2 FL2} =>
                        {D5 : append FL1 FL2 FL12'} =>
                            exists E, {E : eq-list FL12 FL12'}
  H2:{D2 : map ([x]f1 x) L12 FL12}
  H4:{D4 : map ([x]f1 x) L12 FL12'}
  H6:{L12 : list}*
  H7:{n:nat |- f1 n : nat}
  H8:{FL12' : list}
  H9:{E n : eq-list FL12 FL12'}
  
  ==================================
  {E n : eq-list FL12 FL12'}
  
  map-distrib-append.2>> search.
  Proof Completed!
  
  >> Goodbye!
