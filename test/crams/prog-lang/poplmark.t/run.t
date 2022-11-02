  $ adelfa -i 1a.ath
  Welcome!
  >> Specification 1a.lf.
  
  >> Schema c := {U}(w:ty,x:var w,y:bound w U,z:bound_var w U y x);
      {}(x:ty,y:var x); {V T DV}(x:bound V T,y:bound_var V T x DV).
  
  >> Schema wf := {}(x:ty).
  
  >> Theorem sub__ty:
      ctx  L:c,
        forall  D U1 U2,
          {L |- D : sub U1 U2} => {L |- U1 : ty} /\ {L |- U2 : ty}.
  
  Subgoal sub__ty:
  
  
  ==================================
  ctx L:c.
    forall D, forall U1, forall U2,
      {L |- D : sub U1 U2} => {L |- U1 : ty} /\ {L |- U2 : ty}
  
  sub__ty>> intros.
  
  Subgoal sub__ty:
  
  Vars: U2:o, U1:o, D:o
  Contexts: L{}:c[]
  H1:{L |- D : sub U1 U2}
  
  ==================================
  {L |- U1 : ty} /\ {L |- U2 : ty}
  
  sub__ty>> split.
  
  Subgoal sub__ty:
  
  Vars: U2:o, U1:o, D:o
  Contexts: L{}:c[]
  H1:{L |- D : sub U1 U2}
  
  ==================================
  {L |- U1 : ty}
  
  Subgoal sub__ty is:
   {L |- U2 : ty}
  
  sub__ty>> search.
  
  Subgoal sub__ty:
  
  Vars: U2:o, U1:o, D:o
  Contexts: L{}:c[]
  H1:{L |- D : sub U1 U2}
  
  ==================================
  {L |- U2 : ty}
  
  sub__ty>> search.
  Proof Completed!
  
  >> Theorem ty_strengthening:
      ctx  L:c,
        forall  X S DV T:(o) -> (o) -> o,
          {L |- X : ty} =>
            {L |- S : ty} =>
              {L |- DV : var X} =>
                {L |- [x][y]T x y : {x:bound X S}{y:bound_var X S x DV}ty} =>
                  exists  T' Eq,
                    {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}.
  
  Subgoal ty_strengthening:
  
  
  ==================================
  ctx L:c.
    forall X, forall S, forall DV, forall T,
      {L |- X : ty} =>
          {L |- S : ty} =>
              {L |- DV : var X} =>
                  {L |- [x][y]T x y : {x:bound X S}{y:bound_var X S x DV}ty} =>
                      exists T', exists Eq,
                        {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  
  ty_strengthening>> induction on 4.
  
  Subgoal ty_strengthening:
  
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  
  ==================================
  ctx L:c.
    forall X, forall S, forall DV, forall T,
      {L |- X : ty} =>
          {L |- S : ty} =>
              {L |- DV : var X} =>
                  {L |- [x][y]T x y : {x:bound X S}{y:bound_var X S x DV}ty}@
                      =>
                      exists T', exists Eq,
                        {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  
  ty_strengthening>> intros.
  
  Subgoal ty_strengthening:
  
  Vars: T:(o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H4:{L, n:bound X S, n1:bound_var X S n DV |- T n n1 : ty}@
  
  ==================================
  exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  
  ty_strengthening>> cases H4.
  
  Subgoal ty_strengthening.1:
  
  Vars: T1:(o) -> (o) -> o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n2:o, n1:o, n:o
  Contexts: L{n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T1 n1 n : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all (T1 y x) (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> apply IH to H1 H2 H3 H5 with (L = L), X = X, S = S, DV = DV, T =
      [x][y]T1 y x.
  
  Subgoal ty_strengthening.1:
  
  Vars: Eq:(o) -> (o) -> (o) -> o, T':(o) -> (o) -> (o) -> o, T1:
          (o) -> (o) -> o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n2:o, n1:o, n:o
  Contexts: L{n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T1 n1 n : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H7:{L |- Eq n2 n1 n : eq_ty X S DV ([x][y]T1 y x) ([x][y]T' n2 n1 n)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all (T1 y x) (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> prune H7.
  
  Subgoal ty_strengthening.1:
  
  Vars: Eq:o, T':(o) -> (o) -> (o) -> o, T1:(o) -> (o) -> o, F:
          (o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n2:o, n1:o, n:o
  Contexts: L{n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T1 n1 n : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H7:{L |- Eq : eq_ty X S DV ([x][y]T1 y x) ([x][y]T' n2 n1 n)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all (T1 y x) (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> cases H7.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> weaken H6 with var n2.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> ctxpermute H12 to L,n2:ty,n5:var n2,n:bound X S,n1:bound_var X S n DV.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> weaken H1 with ty.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  H14:{L, n6:ty |- X : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> weaken H14 with var n6.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> weaken H2 with ty.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> weaken H16 with var n8.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  H17:{L, n8:ty, n9:var n8 |- S : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> weaken H3 with ty.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  H17:{L, n8:ty, n9:var n8 |- S : ty}
  H18:{L, n10:ty |- DV : var X}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> weaken H18 with var n10.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  H17:{L, n8:ty, n9:var n8 |- S : ty}
  H18:{L, n10:ty |- DV : var X}
  H19:{L, n10:ty, n11:var n10 |- DV : var X}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> apply IH to H15 H17 H19 H13 with (L = L,n1:ty,n:var n1).
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, Eq:
          (o) ->
            (o) ->
              (o) ->
                (o) ->
                  (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o,
          T':
          (o) ->
            (o) ->
              (o) ->
                (o) ->
                  (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o,
          F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  H17:{L, n8:ty, n9:var n8 |- S : ty}
  H18:{L, n10:ty |- DV : var X}
  H19:{L, n10:ty, n11:var n10 |- DV : var X}
  H20:
      {L, n1:ty, n:var n1 |- Eq n11 n10 n9 n8 n7 n6 n5 n4 n3 n2 n1 n :
        eq_ty X S DV ([x][y]F y x n1)
          ([x][y]T' n11 n10 n9 n8 n7 n6 n5 n4 n3 n2 n1 n)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> prune H20.
  
  Subgoal ty_strengthening.1:
  
  Vars: T3:o, Eq:(o) -> (o) -> o, T':
          (o) ->
            (o) ->
              (o) ->
                (o) ->
                  (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o,
          F:(o) -> (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F n1 n n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:
      {L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F n1 n n2 :
        ty}*
  H13:
      {L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F n1 n n2 :
        ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  H17:{L, n8:ty, n9:var n8 |- S : ty}
  H18:{L, n10:ty |- DV : var X}
  H19:{L, n10:ty, n11:var n10 |- DV : var X}
  H20:
      {L, n1:ty, n:var n1 |- Eq n1 n :
        eq_ty X S DV ([x][y]F y x n1)
          ([x][y]T' n11 n10 n9 n8 n7 n6 n5 n4 n3 n2 n1 n)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 (F y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> cases H20.
  
  Subgoal ty_strengthening.1:
  
  Vars: F2:(o) -> o, T3:o, DV:o, S:o, X:o
  Nominals: n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F2 n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:{L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F2 n2 : ty}*
  H13:{L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F2 n2 : ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  H17:{L, n8:ty, n9:var n8 |- S : ty}
  H18:{L, n10:ty |- DV : var X}
  H19:{L, n10:ty, n11:var n10 |- DV : var X}
  H21:{L, n1:ty, n:var n1 |- X : ty}
  H22:{L, n1:ty, n:var n1 |- S : ty}
  H23:{L, n1:ty, n:var n1 |- DV : var X}
  H24:
      {L, n1:ty, n:var n1, n12:bound X S, n13:bound_var X S n12 DV |- F2 n1 :
        ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]all T3 ([z3]F2 z3)) ([x][y]T')}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> exists all T3 ([z3]F2 z3).
  
  Subgoal ty_strengthening.1:
  
  Vars: F2:(o) -> o, T3:o, DV:o, S:o, X:o
  Nominals: n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F2 n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:{L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F2 n2 : ty}*
  H13:{L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F2 n2 : ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  H17:{L, n8:ty, n9:var n8 |- S : ty}
  H18:{L, n10:ty |- DV : var X}
  H19:{L, n10:ty, n11:var n10 |- DV : var X}
  H21:{L, n1:ty, n:var n1 |- X : ty}
  H22:{L, n1:ty, n:var n1 |- S : ty}
  H23:{L, n1:ty, n:var n1 |- DV : var X}
  H24:
      {L, n1:ty, n:var n1, n12:bound X S, n13:bound_var X S n12 DV |- F2 n1 :
        ty}
  
  ==================================
  exists Eq,
    {L |- Eq :
      eq_ty X S DV ([x][y]all T3 ([z3]F2 z3)) ([x][y]all T3 ([z3]F2 z3))}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> exists refl_ty X S DV ([x][y]all T3 ([z3]F2 z3)).
  
  Subgoal ty_strengthening.1:
  
  Vars: F2:(o) -> o, T3:o, DV:o, S:o, X:o
  Nominals: n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T3 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV, n2:ty |- F2 n2 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n3:bound X S, n4:bound_var X S n3 DV |- T3 : ty}
  H12:{L, n:bound X S, n1:bound_var X S n DV, n2:ty, n5:var n2 |- F2 n2 : ty}*
  H13:{L, n2:ty, n5:var n2, n:bound X S, n1:bound_var X S n DV |- F2 n2 : ty}*
  H14:{L, n6:ty |- X : ty}
  H15:{L, n6:ty, n7:var n6 |- X : ty}
  H16:{L, n8:ty |- S : ty}
  H17:{L, n8:ty, n9:var n8 |- S : ty}
  H18:{L, n10:ty |- DV : var X}
  H19:{L, n10:ty, n11:var n10 |- DV : var X}
  H21:{L, n1:ty, n:var n1 |- X : ty}
  H22:{L, n1:ty, n:var n1 |- S : ty}
  H23:{L, n1:ty, n:var n1 |- DV : var X}
  H24:
      {L, n1:ty, n:var n1, n12:bound X S, n13:bound_var X S n12 DV |- F2 n1 :
        ty}
  
  ==================================
  {L |- refl_ty X S DV ([x][y]all T3 ([z3]F2 z3)) :
    eq_ty X S DV ([x][y]all T3 ([z3]F2 z3)) ([x][y]all T3 ([z3]F2 z3))}
  
  Subgoal ty_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.1>> search.
  
  Subgoal ty_strengthening.2:
  
  Vars: T1:(o) -> (o) -> o, T2:(o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T1 n1 n : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV |- T2 n1 n : ty}*
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.2>> apply IH to H1 H2 H3 H5.
  
  Subgoal ty_strengthening.2:
  
  Vars: Eq:(o) -> (o) -> o, T':(o) -> (o) -> o, T1:(o) -> (o) -> o, T2:
          (o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T1 n1 n : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV |- T2 n1 n : ty}*
  H7:{L |- Eq n1 n : eq_ty X S DV ([x][y]T1 y x) ([x][y]T' n1 n)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]arrow (T1 y x) (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.2>> cases H7.
  
  Subgoal ty_strengthening.2:
  
  Vars: T4:o, T2:(o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T4 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV |- T2 n1 n : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n2:bound X S, n3:bound_var X S n2 DV |- T4 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]arrow T4 (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.2>> apply IH to H1 H2 H3 H6.
  
  Subgoal ty_strengthening.2:
  
  Vars: T4:o, Eq:(o) -> (o) -> (o) -> (o) -> o, T':
          (o) -> (o) -> (o) -> (o) -> o, T2:(o) -> (o) -> o, DV:o, S:o, X:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T4 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV |- T2 n1 n : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n2:bound X S, n3:bound_var X S n2 DV |- T4 : ty}
  H12:{L |- Eq n3 n2 n1 n : eq_ty X S DV ([x][y]T2 y x) ([x][y]T' n3 n2 n1 n)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty X S DV ([x][y]arrow T4 (T2 y x)) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.2>> cases H12.
  
  Subgoal ty_strengthening.2:
  
  Vars: T5:o, T4:o, DV:o, S:o, X:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T4 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV |- T5 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n2:bound X S, n3:bound_var X S n2 DV |- T4 : ty}
  H13:{L |- X : ty}
  H14:{L |- S : ty}
  H15:{L |- DV : var X}
  H16:{L, n4:bound X S, n5:bound_var X S n4 DV |- T5 : ty}
  
  ==================================
  exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]arrow T4 T5) ([x][y]T')}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.2>> exists arrow T4 T5.
  
  Subgoal ty_strengthening.2:
  
  Vars: T5:o, T4:o, DV:o, S:o, X:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T4 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV |- T5 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n2:bound X S, n3:bound_var X S n2 DV |- T4 : ty}
  H13:{L |- X : ty}
  H14:{L |- S : ty}
  H15:{L |- DV : var X}
  H16:{L, n4:bound X S, n5:bound_var X S n4 DV |- T5 : ty}
  
  ==================================
  exists Eq, {L |- Eq : eq_ty X S DV ([x][y]arrow T4 T5) ([x][y]arrow T4 T5)}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.2>> exists refl_ty X S DV ([x][y]arrow T4 T5).
  
  Subgoal ty_strengthening.2:
  
  Vars: T5:o, T4:o, DV:o, S:o, X:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n:bound X S, n1:bound_var X S n DV |- T4 : ty}*
  H6:{L, n:bound X S, n1:bound_var X S n DV |- T5 : ty}*
  H8:{L |- X : ty}
  H9:{L |- S : ty}
  H10:{L |- DV : var X}
  H11:{L, n2:bound X S, n3:bound_var X S n2 DV |- T4 : ty}
  H13:{L |- X : ty}
  H14:{L |- S : ty}
  H15:{L |- DV : var X}
  H16:{L, n4:bound X S, n5:bound_var X S n4 DV |- T5 : ty}
  
  ==================================
  {L |- refl_ty X S DV ([x][y]arrow T4 T5) :
    eq_ty X S DV ([x][y]arrow T4 T5) ([x][y]arrow T4 T5)}
  
  Subgoal ty_strengthening.3 is:
   exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.2>> search.
  
  Subgoal ty_strengthening.3:
  
  Vars: DV:o, S:o, X:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  
  ==================================
  exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.3>> weaken H1 with bound X S.
  
  Subgoal ty_strengthening.3:
  
  Vars: DV:o, S:o, X:o
  Nominals: n2:o, n1:o, n:o
  Contexts: L{n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n2:bound X S |- X : ty}
  
  ==================================
  exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.3>> weaken H2 with bound X S.
  
  Subgoal ty_strengthening.3:
  
  Vars: DV:o, S:o, X:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n2:bound X S |- X : ty}
  H6:{L, n3:bound X S |- S : ty}
  
  ==================================
  exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.3>> weaken H3 with bound X S.
  
  Subgoal ty_strengthening.3:
  
  Vars: DV:o, S:o, X:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n2:bound X S |- X : ty}
  H6:{L, n3:bound X S |- S : ty}
  H7:{L, n4:bound X S |- DV : var X}
  
  ==================================
  exists T', exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]T')}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.3>> exists top.
  
  Subgoal ty_strengthening.3:
  
  Vars: DV:o, S:o, X:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n2:bound X S |- X : ty}
  H6:{L, n3:bound X S |- S : ty}
  H7:{L, n4:bound X S |- DV : var X}
  
  ==================================
  exists Eq, {L |- Eq : eq_ty X S DV ([x][y]top) ([x][y]top)}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.3>> exists refl_ty X S DV ([x][y]top).
  
  Subgoal ty_strengthening.3:
  
  Vars: DV:o, S:o, X:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H5:{L, n2:bound X S |- X : ty}
  H6:{L, n3:bound X S |- S : ty}
  H7:{L, n4:bound X S |- DV : var X}
  
  ==================================
  {L |- refl_ty X S DV ([x][y]top) : eq_ty X S DV ([x][y]top) ([x][y]top)}
  
  Subgoal ty_strengthening.4 is:
   exists T', exists Eq,
     {L |- Eq :
       eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
         ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.3>> search.
  
  Subgoal ty_strengthening.4:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U n2 n3 n4 n5), n5:
              bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq :
      eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
        ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.4>> weaken H1 with bound X n2 n3 n4 n5 S n2 n3 n4 n5.
  
  Subgoal ty_strengthening.4:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U n2 n3 n4 n5), n5:
              bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq :
      eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
        ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.4>> weaken H2 with bound X n2 n3 n4 n5 S n2 n3 n4 n5.
  
  Subgoal ty_strengthening.4:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U n2 n3 n4 n5),
              n5:bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  H6:{L, n7:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- S n2 n3 n4 n5 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq :
      eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
        ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.4>> weaken H3 with bound X n2 n3 n4 n5 S n2 n3 n4 n5.
  
  Subgoal ty_strengthening.4:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:
              bound n2 (U n2 n3 n4 n5), n5:bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  H6:{L, n7:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- S n2 n3 n4 n5 : ty}
  H7:
      {L, n8:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- DV n2 n3 n4 n5 :
        var (X n2 n3 n4 n5)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq :
      eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
        ([x][y]T')}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.4>> exists n2.
  
  Subgoal ty_strengthening.4:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:
              bound n2 (U n2 n3 n4 n5), n5:bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  H6:{L, n7:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- S n2 n3 n4 n5 : ty}
  H7:
      {L, n8:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- DV n2 n3 n4 n5 :
        var (X n2 n3 n4 n5)}
  
  ==================================
  exists Eq,
    {L |- Eq :
      eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
        ([x][y]n2)}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.4>> exists refl_ty X n2 n3 n4 n5 S n2 n3 n4 n5 DV n2 n3 n4 n5 ([x][y]n2).
  
  Subgoal ty_strengthening.4:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:
              bound n2 (U n2 n3 n4 n5), n5:bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  H6:{L, n7:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- S n2 n3 n4 n5 : ty}
  H7:
      {L, n8:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- DV n2 n3 n4 n5 :
        var (X n2 n3 n4 n5)}
  
  ==================================
  {L |- refl_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2) :
    eq_ty (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n2)
      ([x][y]n2)}
  
  Subgoal ty_strengthening.5 is:
   exists T', exists Eq,
     {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.4>> search.
  
  Subgoal ty_strengthening.5:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.5>> weaken H1 with bound X n2 n3 S n2 n3.
  
  Subgoal ty_strengthening.5:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.5>> weaken H2 with bound X n2 n3 S n2 n3.
  
  Subgoal ty_strengthening.5:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  H6:{L, n5:bound (X n2 n3) (S n2 n3) |- S n2 n3 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.5>> weaken H3 with bound X n2 n3 S n2 n3.
  
  Subgoal ty_strengthening.5:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  H6:{L, n5:bound (X n2 n3) (S n2 n3) |- S n2 n3 : ty}
  H7:{L, n6:bound (X n2 n3) (S n2 n3) |- DV n2 n3 : var (X n2 n3)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]T')}
  
  ty_strengthening.5>> exists n2.
  
  Subgoal ty_strengthening.5:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  H6:{L, n5:bound (X n2 n3) (S n2 n3) |- S n2 n3 : ty}
  H7:{L, n6:bound (X n2 n3) (S n2 n3) |- DV n2 n3 : var (X n2 n3)}
  
  ==================================
  exists Eq,
    {L |- Eq : eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]n2)}
  
  ty_strengthening.5>> exists refl_ty X n2 n3 S n2 n3 DV n2 n3 ([x][y]n2).
  
  Subgoal ty_strengthening.5:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}ty}* =>
                          exists T', exists Eq,
                            {L |- Eq : eq_ty X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  H6:{L, n5:bound (X n2 n3) (S n2 n3) |- S n2 n3 : ty}
  H7:{L, n6:bound (X n2 n3) (S n2 n3) |- DV n2 n3 : var (X n2 n3)}
  
  ==================================
  {L |- refl_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) :
    eq_ty (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n2) ([x][y]n2)}
  
  ty_strengthening.5>> search.
  Proof Completed!
  
  >> Theorem var_strengthening:
      ctx  L:c,
        forall  Q X S DV T:(o) -> (o) -> o,
          {L |- X : ty} =>
            {L |- S : ty} =>
              {L |- DV : var X} =>
                {L |- [x][y]T x y : {x:bound X S}{y:bound_var X S x DV}var Q}
                  =>
                  exists  T' Eq,
                    {L |- Eq : eq_var Q X S DV ([x][y]T x y) ([x][y]T')}.
  
  Subgoal var_strengthening:
  
  
  ==================================
  ctx L:c.
    forall Q, forall X, forall S, forall DV, forall T,
      {L |- X : ty} =>
          {L |- S : ty} =>
              {L |- DV : var X} =>
                  {L |- [x][y]T x y : {x:bound X S}{y:bound_var X S x DV}var Q}
                      =>
                      exists T', exists Eq,
                        {L |- Eq : eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  
  var_strengthening>> induction on 4.
  
  Subgoal var_strengthening:
  
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  
  ==================================
  ctx L:c.
    forall Q, forall X, forall S, forall DV, forall T,
      {L |- X : ty} =>
          {L |- S : ty} =>
              {L |- DV : var X} =>
                  {L |- [x][y]T x y :
                    {x:bound X S}{y:bound_var X S x DV}var Q}@ =>
                      exists T', exists Eq,
                        {L |- Eq : eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  
  var_strengthening>> intros.
  
  Subgoal var_strengthening:
  
  Vars: T:(o) -> (o) -> o, DV:o, S:o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X : ty}
  H2:{L |- S : ty}
  H3:{L |- DV : var X}
  H4:{L, n:bound X S, n1:bound_var X S n DV |- T n n1 : var Q}@
  
  ==================================
  exists T', exists Eq, {L |- Eq : eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  
  var_strengthening>> cases H4.
  
  Subgoal var_strengthening.1:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U n2 n3 n4 n5), n5:
              bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq :
      eq_var n2 (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n3)
        ([x][y]T')}
  
  Subgoal var_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.1>> weaken H1 with bound X n2 n3 n4 n5 S n2 n3 n4 n5.
  
  Subgoal var_strengthening.1:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U n2 n3 n4 n5), n5:
              bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq :
      eq_var n2 (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n3)
        ([x][y]T')}
  
  Subgoal var_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.1>> weaken H2 with bound X n2 n3 n4 n5 S n2 n3 n4 n5.
  
  Subgoal var_strengthening.1:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U n2 n3 n4 n5),
              n5:bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  H6:{L, n7:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- S n2 n3 n4 n5 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq :
      eq_var n2 (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n3)
        ([x][y]T')}
  
  Subgoal var_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.1>> weaken H3 with bound X n2 n3 n4 n5 S n2 n3 n4 n5.
  
  Subgoal var_strengthening.1:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:
              bound n2 (U n2 n3 n4 n5), n5:bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  H6:{L, n7:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- S n2 n3 n4 n5 : ty}
  H7:
      {L, n8:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- DV n2 n3 n4 n5 :
        var (X n2 n3 n4 n5)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq :
      eq_var n2 (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n3)
        ([x][y]T')}
  
  Subgoal var_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.1>> exists n3.
  
  Subgoal var_strengthening.1:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:
              bound n2 (U n2 n3 n4 n5), n5:bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  H6:{L, n7:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- S n2 n3 n4 n5 : ty}
  H7:
      {L, n8:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- DV n2 n3 n4 n5 :
        var (X n2 n3 n4 n5)}
  
  ==================================
  exists Eq,
    {L |- Eq :
      eq_var n2 (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n3)
        ([x][y]n3)}
  
  Subgoal var_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.1>> exists refl_var n2 X n2 n3 n4 n5 S n2 n3 n4 n5 DV n2 n3 n4 n5 ([x][y]n3).
  
  Subgoal var_strengthening.1:
  
  Vars: U:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, S:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:
              bound n2 (U n2 n3 n4 n5), n5:bound_var n2 (U n2 n3 n4 n5) n4 n3)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 n4 n5 : ty}
  H2:{L |- S n2 n3 n4 n5 : ty}
  H3:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L, n6:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- X n2 n3 n4 n5 : ty}
  H6:{L, n7:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- S n2 n3 n4 n5 : ty}
  H7:
      {L, n8:bound (X n2 n3 n4 n5) (S n2 n3 n4 n5) |- DV n2 n3 n4 n5 :
        var (X n2 n3 n4 n5)}
  
  ==================================
  {L |- refl_var n2 (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n3)
    :
    eq_var n2 (X n2 n3 n4 n5) (S n2 n3 n4 n5) (DV n2 n3 n4 n5) ([x][y]n3)
      ([x][y]n3)}
  
  Subgoal var_strengthening.2 is:
   exists T', exists Eq,
     {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.1>> search.
  
  Subgoal var_strengthening.2:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.2>> weaken H1 with bound X n2 n3 S n2 n3.
  
  Subgoal var_strengthening.2:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.2>> weaken H2 with bound X n2 n3 S n2 n3.
  
  Subgoal var_strengthening.2:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  H6:{L, n5:bound (X n2 n3) (S n2 n3) |- S n2 n3 : ty}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.2>> weaken H3 with bound X n2 n3 S n2 n3.
  
  Subgoal var_strengthening.2:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  H6:{L, n5:bound (X n2 n3) (S n2 n3) |- S n2 n3 : ty}
  H7:{L, n6:bound (X n2 n3) (S n2 n3) |- DV n2 n3 : var (X n2 n3)}
  
  ==================================
  exists T', exists Eq,
    {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]T')}
  
  var_strengthening.2>> exists n3.
  
  Subgoal var_strengthening.2:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  H6:{L, n5:bound (X n2 n3) (S n2 n3) |- S n2 n3 : ty}
  H7:{L, n6:bound (X n2 n3) (S n2 n3) |- DV n2 n3 : var (X n2 n3)}
  
  ==================================
  exists Eq,
    {L |- Eq : eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]n3)}
  
  var_strengthening.2>> exists refl_var n2 X n2 n3 S n2 n3 DV n2 n3 ([x][y]n3).
  
  Subgoal var_strengthening.2:
  
  Vars: DV:(o) -> (o) -> o, S:(o) -> (o) -> o, X:(o) -> (o) -> o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n1, n}:c[(n2:ty, n3:var n2)]
  IH:
      ctx L:c.
        forall Q, forall X, forall S, forall DV, forall T,
          {L |- X : ty} =>
              {L |- S : ty} =>
                  {L |- DV : var X} =>
                      {L |- [x][y]T x y :
                        {x:bound X S}{y:bound_var X S x DV}var Q}* =>
                          exists T', exists Eq,
                            {L |- Eq :
                              eq_var Q X S DV ([x][y]T x y) ([x][y]T')}
  H1:{L |- X n2 n3 : ty}
  H2:{L |- S n2 n3 : ty}
  H3:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L, n4:bound (X n2 n3) (S n2 n3) |- X n2 n3 : ty}
  H6:{L, n5:bound (X n2 n3) (S n2 n3) |- S n2 n3 : ty}
  H7:{L, n6:bound (X n2 n3) (S n2 n3) |- DV n2 n3 : var (X n2 n3)}
  
  ==================================
  {L |- refl_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) :
    eq_var n2 (X n2 n3) (S n2 n3) (DV n2 n3) ([x][y]n3) ([x][y]n3)}
  
  var_strengthening.2>> search.
  Proof Completed!
  
  >> Theorem narrow_ty:
      ctx  L:c,
        forall  Q X P D T:(o) -> (o) -> o DV,
          {L |- X : ty} =>
            {L |- DV : var X} =>
              {L |- D : sub P Q} =>
                {L |- [x][y]T x y : {x:bound X Q}{y:bound_var X Q x DV}ty} =>
                  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}ty}.
  
  Subgoal narrow_ty:
  
  
  ==================================
  ctx L:c.
    forall Q, forall X, forall P, forall D, forall T, forall DV,
      {L |- X : ty} =>
          {L |- DV : var X} =>
              {L |- D : sub P Q} =>
                  {L |- [x][y]T x y : {x:bound X Q}{y:bound_var X Q x DV}ty} =>
                      {L |- [x][y]T x y :
                        {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> intros.
  
  Subgoal narrow_ty:
  
  Vars: DV:o, T:(o) -> (o) -> o, D:o, P:o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T n n1 : ty}
  
  ==================================
  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> apply sub__ty to H3.
  
  Subgoal narrow_ty:
  
  Vars: DV:o, T:(o) -> (o) -> o, D:o, P:o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T n n1 : ty}
  H5:{L |- P : ty} /\ {L |- Q : ty}
  
  ==================================
  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> cases H5.
  
  Subgoal narrow_ty:
  
  Vars: DV:o, T:(o) -> (o) -> o, D:o, P:o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T n n1 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  
  ==================================
  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> apply ty_strengthening to H1 H7 H2 H4.
  
  Subgoal narrow_ty:
  
  Vars: Eq:(o) -> (o) -> o, T':(o) -> (o) -> o, DV:o, T:(o) -> (o) -> o, D:o, P
          :o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T n n1 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H8:{L |- Eq n1 n : eq_ty X Q DV ([x][y]T x y) ([x][y]T' n1 n)}
  
  ==================================
  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> cases H8.
  
  Subgoal narrow_ty:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- X : ty}
  H10:{L |- Q : ty}
  H11:{L |- DV : var X}
  H12:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> strengthen H12.
  
  Subgoal narrow_ty:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- X : ty}
  H10:{L |- Q : ty}
  H11:{L |- DV : var X}
  H12:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : ty}
  H13:{L, n2:bound X Q |- T2 : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> strengthen H13.
  
  Subgoal narrow_ty:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- X : ty}
  H10:{L |- Q : ty}
  H11:{L |- DV : var X}
  H12:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : ty}
  H13:{L, n2:bound X Q |- T2 : ty}
  H14:{L |- T2 : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> weaken H1 with bound X P.
  
  Subgoal narrow_ty:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- X : ty}
  H10:{L |- Q : ty}
  H11:{L |- DV : var X}
  H12:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : ty}
  H13:{L, n2:bound X Q |- T2 : ty}
  H14:{L |- T2 : ty}
  H15:{L, n4:bound X P |- X : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> weaken H6 with bound X P.
  
  Subgoal narrow_ty:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- X : ty}
  H10:{L |- Q : ty}
  H11:{L |- DV : var X}
  H12:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : ty}
  H13:{L, n2:bound X Q |- T2 : ty}
  H14:{L |- T2 : ty}
  H15:{L, n4:bound X P |- X : ty}
  H16:{L, n5:bound X P |- P : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> weaken H2 with bound X P.
  
  Subgoal narrow_ty:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- X : ty}
  H10:{L |- Q : ty}
  H11:{L |- DV : var X}
  H12:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : ty}
  H13:{L, n2:bound X Q |- T2 : ty}
  H14:{L |- T2 : ty}
  H15:{L, n4:bound X P |- X : ty}
  H16:{L, n5:bound X P |- P : ty}
  H17:{L, n6:bound X P |- DV : var X}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> weaken H14 with bound X P.
  
  Subgoal narrow_ty:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n5, n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- X : ty}
  H10:{L |- Q : ty}
  H11:{L |- DV : var X}
  H12:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : ty}
  H13:{L, n2:bound X Q |- T2 : ty}
  H14:{L |- T2 : ty}
  H15:{L, n4:bound X P |- X : ty}
  H16:{L, n5:bound X P |- P : ty}
  H17:{L, n6:bound X P |- DV : var X}
  H18:{L, n7:bound X P |- T2 : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> weaken H18 with bound_var X P n7 DV.
  
  Subgoal narrow_ty:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : ty}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- X : ty}
  H10:{L |- Q : ty}
  H11:{L |- DV : var X}
  H12:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : ty}
  H13:{L, n2:bound X Q |- T2 : ty}
  H14:{L |- T2 : ty}
  H15:{L, n4:bound X P |- X : ty}
  H16:{L, n5:bound X P |- P : ty}
  H17:{L, n6:bound X P |- DV : var X}
  H18:{L, n7:bound X P |- T2 : ty}
  H19:{L, n7:bound X P, n8:bound_var X P n7 DV |- T2 : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}ty}
  
  narrow_ty>> search.
  Proof Completed!
  
  >> Theorem narrow_var:
      ctx  L:c,
        forall  S Q X P D T:(o) -> (o) -> o DV,
          {L |- X : ty} =>
            {L |- DV : var X} =>
              {L |- D : sub P Q} =>
                {L |- [x][y]T x y : {x:bound X Q}{y:bound_var X Q x DV}var S}
                  =>
                  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}var S}.
  
  Subgoal narrow_var:
  
  
  ==================================
  ctx L:c.
    forall S, forall Q, forall X, forall P, forall D, forall T, forall DV,
      {L |- X : ty} =>
          {L |- DV : var X} =>
              {L |- D : sub P Q} =>
                  {L |- [x][y]T x y : {x:bound X Q}{y:bound_var X Q x DV}var S}
                      =>
                      {L |- [x][y]T x y :
                        {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> intros.
  
  Subgoal narrow_var:
  
  Vars: DV:o, T:(o) -> (o) -> o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T n n1 : var S}
  
  ==================================
  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> apply sub__ty to H3.
  
  Subgoal narrow_var:
  
  Vars: DV:o, T:(o) -> (o) -> o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T n n1 : var S}
  H5:{L |- P : ty} /\ {L |- Q : ty}
  
  ==================================
  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> cases H5.
  
  Subgoal narrow_var:
  
  Vars: DV:o, T:(o) -> (o) -> o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T n n1 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  
  ==================================
  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> apply var_strengthening to H1 H7 H2 H4.
  
  Subgoal narrow_var:
  
  Vars: Eq:(o) -> (o) -> o, T':(o) -> (o) -> o, DV:o, T:(o) -> (o) -> o, D:o, P
          :o, X:o, Q:o, S:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T n n1 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H8:{L |- Eq n1 n : eq_var S X Q DV ([x][y]T x y) ([x][y]T' n1 n)}
  
  ==================================
  {L |- [x][y]T x y : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> cases H8.
  
  Subgoal narrow_var:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- S : ty}
  H10:{L |- X : ty}
  H11:{L |- Q : ty}
  H12:{L |- DV : var X}
  H13:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : var S}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> strengthen H13.
  
  Subgoal narrow_var:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- S : ty}
  H10:{L |- X : ty}
  H11:{L |- Q : ty}
  H12:{L |- DV : var X}
  H13:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : var S}
  H14:{L, n2:bound X Q |- T2 : var S}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> strengthen H14.
  
  Subgoal narrow_var:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- S : ty}
  H10:{L |- X : ty}
  H11:{L |- Q : ty}
  H12:{L |- DV : var X}
  H13:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : var S}
  H14:{L, n2:bound X Q |- T2 : var S}
  H15:{L |- T2 : var S}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> weaken H1 with bound X P.
  
  Subgoal narrow_var:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- S : ty}
  H10:{L |- X : ty}
  H11:{L |- Q : ty}
  H12:{L |- DV : var X}
  H13:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : var S}
  H14:{L, n2:bound X Q |- T2 : var S}
  H15:{L |- T2 : var S}
  H16:{L, n4:bound X P |- X : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> weaken H6 with bound X P.
  
  Subgoal narrow_var:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- S : ty}
  H10:{L |- X : ty}
  H11:{L |- Q : ty}
  H12:{L |- DV : var X}
  H13:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : var S}
  H14:{L, n2:bound X Q |- T2 : var S}
  H15:{L |- T2 : var S}
  H16:{L, n4:bound X P |- X : ty}
  H17:{L, n5:bound X P |- P : ty}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> weaken H2 with bound X P.
  
  Subgoal narrow_var:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- S : ty}
  H10:{L |- X : ty}
  H11:{L |- Q : ty}
  H12:{L |- DV : var X}
  H13:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : var S}
  H14:{L, n2:bound X Q |- T2 : var S}
  H15:{L |- T2 : var S}
  H16:{L, n4:bound X P |- X : ty}
  H17:{L, n5:bound X P |- P : ty}
  H18:{L, n6:bound X P |- DV : var X}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> weaken H15 with bound X P.
  
  Subgoal narrow_var:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n5, n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- S : ty}
  H10:{L |- X : ty}
  H11:{L |- Q : ty}
  H12:{L |- DV : var X}
  H13:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : var S}
  H14:{L, n2:bound X Q |- T2 : var S}
  H15:{L |- T2 : var S}
  H16:{L, n4:bound X P |- X : ty}
  H17:{L, n5:bound X P |- P : ty}
  H18:{L, n6:bound X P |- DV : var X}
  H19:{L, n7:bound X P |- T2 : var S}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> weaken H19 with bound_var X P n7 DV.
  
  Subgoal narrow_var:
  
  Vars: T2:o, DV:o, D:o, P:o, X:o, Q:o, S:o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n5, n4, n3, n2, n1, n}:c[]
  H1:{L |- X : ty}
  H2:{L |- DV : var X}
  H3:{L |- D : sub P Q}
  H4:{L, n:bound X Q, n1:bound_var X Q n DV |- T2 : var S}
  H6:{L |- P : ty}
  H7:{L |- Q : ty}
  H9:{L |- S : ty}
  H10:{L |- X : ty}
  H11:{L |- Q : ty}
  H12:{L |- DV : var X}
  H13:{L, n2:bound X Q, n3:bound_var X Q n2 DV |- T2 : var S}
  H14:{L, n2:bound X Q |- T2 : var S}
  H15:{L |- T2 : var S}
  H16:{L, n4:bound X P |- X : ty}
  H17:{L, n5:bound X P |- P : ty}
  H18:{L, n6:bound X P |- DV : var X}
  H19:{L, n7:bound X P |- T2 : var S}
  H20:{L, n7:bound X P, n8:bound_var X P n7 DV |- T2 : var S}
  
  ==================================
  {L |- [x][y]T2 : {x:bound X P}{y:bound_var X P x DV}var S}
  
  narrow_var>> search.
  Proof Completed!
  
  >> Theorem trans_and_narrow':
      forall  Q,
        ctx  G:wf,
          {G |- Q : ty} =>
            ctx  L:c,
              forall  S T D1 D2,
                {L |- D1 : sub S Q} =>
                  {L |- D2 : sub Q T} => exists  D3, {L |- D3 : sub S T} /\
                  ctx  L:c,
                    forall  X M N P D1 D2:(o) -> (o) -> o DV,
                      {L |- X : ty} =>
                        {L |- DV : var X} =>
                          {L |- D1 : sub P Q} =>
                            {L |- [x][y]D2 x y :
                              {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                              exists  D4:(o) -> (o) -> o,
                                {L |- [x][y]D4 x y :
                                  {x:bound X P}{y:bound_var X P x DV}sub M N}.
  
  Subgoal trans_and_narrow':
  
  
  ==================================
  forall Q,
    ctx G:wf.
      {G |- Q : ty} =>
          ctx L:c.
            forall S, forall T, forall D1, forall D2,
              {L |- D1 : sub S Q} =>
                  {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
              /\
              ctx L:c.
                forall X, forall M, forall N, forall P, forall D1, forall D2,
                  forall DV,
                  {L |- X : ty} =>
                      {L |- DV : var X} =>
                          {L |- D1 : sub P Q} =>
                              {L |- [x][y]D2 x y :
                                {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                                  exists D4,
                                    {L |- [x][y]D4 x y :
                                      {x:bound X P
                                        }{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> induction on 1.
  
  Subgoal trans_and_narrow':
  
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  
  ==================================
  forall Q,
    ctx G:wf.
      {G |- Q : ty}@ =>
          ctx L:c.
            forall S, forall T, forall D1, forall D2,
              {L |- D1 : sub S Q} =>
                  {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
              /\
              ctx L:c.
                forall X, forall M, forall N, forall P, forall D1, forall D2,
                  forall DV,
                  {L |- X : ty} =>
                      {L |- DV : var X} =>
                          {L |- D1 : sub P Q} =>
                              {L |- [x][y]D2 x y :
                                {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                                  exists D4,
                                    {L |- [x][y]D4 x y :
                                      {x:bound X P
                                        }{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> intros.
  
  Subgoal trans_and_narrow':
  
  Vars: Q:o
  Contexts: G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  
  ==================================
  ctx L:c.
    forall S, forall T, forall D1, forall D2,
      {L |- D1 : sub S Q} =>
          {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
      /\
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> assert ctx  L:c,
           forall  S T D1 D2,
             {L |- D1 : sub S Q} =>
               {L |- D2 : sub Q T} => exists  D3, {L |- D3 : sub S T}.
  
  Subgoal trans_and_narrow':
  
  Vars: Q:o
  Contexts: G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  
  ==================================
  ctx L:c.
    forall S, forall T, forall D1, forall D2,
      {L |- D1 : sub S Q} =>
          {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> induction on 1.
  
  Subgoal trans_and_narrow':
  
  Vars: Q:o
  Contexts: G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  
  ==================================
  ctx L:c.
    forall S, forall T, forall D1, forall D2,
      {L |- D1 : sub S Q}@@ =>
          {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> intros.
  
  Subgoal trans_and_narrow':
  
  Vars: D2:o, D1:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- D1 : sub S Q}@@
  H3:{L |- D2 : sub Q T}
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> cases H2.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, T2:
          (o) -> o, D2:o, T:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T2 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T2 x))}** =>
              {L |- D2 : sub (all T1 ([x]T2 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 T2 a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}@@
  H3:{L |- D2 : sub (all T1 ([x]T2 x)) T}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T2 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T2 n2)}**
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1>> cases H3.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o, a1:o, a2:
          (o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, T2:(o) -> o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T2 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T2 x))}** =>
              {L |- D2 : sub (all T1 ([x]T2 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 T2 a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T2 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T2 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T2 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T2 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T2 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T2 n8) (T4 n8)}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> cases H1.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> apply IH to H16 with (G = G), Q = T1.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H18:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
          /\
          ctx L135:c.
            forall X, forall M, forall N, forall P, forall D1, forall D2,
              forall DV,
              {L135 |- X : ty} =>
                  {L135 |- DV : var X} =>
                      {L135 |- D1 : sub P T1} =>
                          {L135 |- [x][y]D2 x y :
                            {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                              exists D4,
                                {L135 |- [x][y]D4 x y :
                                  {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> cases H18.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> apply IH to H17 with (G = G,n12:ty), Q = T5 n12.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H21:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
          /\
          ctx L7911:c.
            forall X, forall M, forall N, forall P, forall D1, forall D2,
              forall DV,
              {L7911 |- X : ty} =>
                  {L7911 |- DV : var X} =>
                      {L7911 |- D1 : sub P (T5 n12)} =>
                          {L7911 |- [x][y]D2 x y :
                            {x:bound X (T5 n12)
                              }{y:bound_var X (T5 n12) x DV}sub M N} =>
                              exists D4,
                                {L7911 |- [x][y]D4 x y :
                                  {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> cases H21.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> apply H19 to H14 H8 with S = T3, T = S1, D1 = D3, D2 = a1.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D1:
          (o) ->
            (o) ->
              (o) ->
                (o) ->
                  (o) ->
                    (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 n11 n10 n9 n8 n7 n6 n5 n4 n3 n2 n1 n : sub T3 S1}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> prune H24.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D1:
          (o) -> o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> assert {L,n:ty,n1:var n |- D3 : sub T3 T1}.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D1:
          (o) -> o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  
  ==================================
  {L, n:ty, n1:var n |- D3 : sub T3 T1}
  
  Subgoal trans_and_narrow'.1.1 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> weaken H14 with ty.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D1:
          (o) -> o
  Nominals: n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n13, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}
              :wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n13:ty |- D3 : sub T3 T1}
  
  ==================================
  {L, n:ty, n1:var n |- D3 : sub T3 T1}
  
  Subgoal trans_and_narrow'.1.1 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> weaken H25 with var n13.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D1:
          (o) -> o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n13:ty |- D3 : sub T3 T1}
  H26:{L, n13:ty, n14:var n13 |- D3 : sub T3 T1}
  
  ==================================
  {L, n:ty, n1:var n |- D3 : sub T3 T1}
  
  Subgoal trans_and_narrow'.1.1 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> search.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D1:
          (o) -> o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n:ty, n1:var n |- D3 : sub T3 T1}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> assert {L,n:ty,n1:var n |- n : ty}.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D1:
          (o) -> o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n:ty, n1:var n |- D3 : sub T3 T1}
  H26:{L, n:ty, n1:var n |- n : ty}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> assert {L,n:ty,n1:var n |- n1 : var n}.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D1:
          (o) -> o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n:ty, n1:var n |- D3 : sub T3 T1}
  H26:{L, n:ty, n1:var n |- n : ty}
  H27:{L, n:ty, n1:var n |- n1 : var n}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> apply H20 to H26 H27 H25 H9 with (L135 = L,n1:ty,n:var n1).
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D2:
          (o) ->
            (o) ->
              (o) ->
                (o) ->
                  (o) ->
                    (o) ->
                      (o) ->
                        (o) ->
                          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o,
          D1:(o) -> o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n:ty, n1:var n |- D3 : sub T3 T1}
  H26:{L, n:ty, n1:var n |- n : ty}
  H27:{L, n:ty, n1:var n |- n1 : var n}
  H28:
      {L, n1:ty, n:var n1, n13:bound n1 T3, n14:bound_var n1 T3 n13 n |- 
        D2 n12 n11 n10 n9 n8 n7 n6 n5 n4 n3 n2 n1 n n13 n14 :
        sub (S2 n1) (T5 n1)}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> prune H28.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o,
          a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D2:
          (o) -> (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n:ty, n1:var n |- D3 : sub T3 T1}
  H26:{L, n:ty, n1:var n |- n : ty}
  H27:{L, n:ty, n1:var n |- n1 : var n}
  H28:
      {L, n1:ty, n:var n1, n13:bound n1 T3, n14:bound_var n1 T3 n13 n |- 
        D2 n12 n1 n n13 n14 : sub (S2 n1) (T5 n1)}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> apply H22 to H28 H15 with (L81012 = L,n12:ty,n1:var n12,n2:bound n12 T3,
      n:bound_var n12 T3 n2 n1).
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: D5:
          (o) ->
            (o) ->
              (o) ->
                (o) ->
                  (o) ->
                    (o) ->
                      (o) ->
                        (o) ->
                          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o,
          T5:(o) -> o, D3:o, D4:(o) -> (o) -> (o) -> (o) -> o, T3:o, T4:
          (o) -> o, a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o,
          T1:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n:ty, n1:var n |- D3 : sub T3 T1}
  H26:{L, n:ty, n1:var n |- n : ty}
  H27:{L, n:ty, n1:var n |- n1 : var n}
  H28:
      {L, n1:ty, n:var n1, n13:bound n1 T3, n14:bound_var n1 T3 n13 n |- 
        D2 n12 n1 n n13 n14 : sub (S2 n1) (T5 n1)}
  H29:
      {L, n12:ty, n1:var n12, n2:bound n12 T3, n:bound_var n12 T3 n2 n1 |- 
        D5 n14 n13 n12 n11 n10 n9 n8 n7 n6 n5 n4 n3 n2 n1 n :
        sub (S2 n12) (T4 n12)}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> prune H29.
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: D5:(o) -> (o) -> (o) -> (o) -> o, T5:(o) -> o, D3:o, D4:
          (o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o, a1:o, a2:
          (o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D2:
          (o) -> (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n:ty, n1:var n |- D3 : sub T3 T1}
  H26:{L, n:ty, n1:var n |- n : ty}
  H27:{L, n:ty, n1:var n |- n1 : var n}
  H28:
      {L, n1:ty, n:var n1, n13:bound n1 T3, n14:bound_var n1 T3 n13 n |- 
        D2 n12 n1 n n13 n14 : sub (S2 n1) (T5 n1)}
  H29:
      {L, n12:ty, n1:var n12, n2:bound n12 T3, n:bound_var n12 T3 n2 n1 |- 
        D5 n12 n2 n1 n : sub (S2 n12) (T4 n12)}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> exists sa-all S1 ([x]S2 x) T3 ([x]T4 x) D1 n12 ([w][x][y][z]D5 w y x z).
  
  Subgoal trans_and_narrow'.1.1:
  
  Vars: D5:(o) -> (o) -> (o) -> (o) -> o, T5:(o) -> o, D3:o, D4:
          (o) -> (o) -> (o) -> (o) -> o, T3:o, T4:(o) -> o, a1:o, a2:
          (o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, D2:
          (o) -> (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{n12}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T5 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T5 x))}** =>
              {L |- D2 : sub (all T1 ([x]T5 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 ([z1]T5 z1) a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T5 x))}@@
  H3:
      {L |- sa-all T1 ([z7]T5 z7) T3 ([z7]T4 z7) D3 D4 :
        sub (all T1 ([x]T5 x)) (all T3 ([x]T4 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T5 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T5 n2)}**
  H10:{L |- T1 : ty}
  H11:{L, n6:ty |- T5 n6 : ty}
  H12:{L |- T3 : ty}
  H13:{L, n7:ty |- T4 n7 : ty}
  H14:{L |- D3 : sub T3 T1}
  H15:
      {L, n8:ty, n9:var n8, n10:bound n8 T3, n11:bound_var n8 T3 n10 n9 |- 
        D4 n8 n9 n10 n11 : sub (T5 n8) (T4 n8)}
  H16:{G |- T1 : ty}*
  H17:{G, n12:ty |- T5 n12 : ty}*
  H19:
      ctx L246:c.
        forall S, forall T, forall D1, forall D2,
          {L246 |- D1 : sub S T1} =>
              {L246 |- D2 : sub T1 T} => exists D3, {L246 |- D3 : sub S T}
  H20:
      ctx L135:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L135 |- X : ty} =>
              {L135 |- DV : var X} =>
                  {L135 |- D1 : sub P T1} =>
                      {L135 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L135 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L81012:c.
        forall S, forall T, forall D1, forall D2,
          {L81012 |- D1 : sub S (T5 n12)} =>
              {L81012 |- D2 : sub (T5 n12) T} =>
                  exists D3, {L81012 |- D3 : sub S T}
  H23:
      ctx L7911:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L7911 |- X : ty} =>
              {L7911 |- DV : var X} =>
                  {L7911 |- D1 : sub P (T5 n12)} =>
                      {L7911 |- [x][y]D2 x y :
                        {x:bound X (T5 n12)
                          }{y:bound_var X (T5 n12) x DV}sub M N} =>
                          exists D4,
                            {L7911 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D1 n12 : sub T3 S1}
  H25:{L, n:ty, n1:var n |- D3 : sub T3 T1}
  H26:{L, n:ty, n1:var n |- n : ty}
  H27:{L, n:ty, n1:var n |- n1 : var n}
  H28:
      {L, n1:ty, n:var n1, n13:bound n1 T3, n14:bound_var n1 T3 n13 n |- 
        D2 n12 n1 n n13 n14 : sub (S2 n1) (T5 n1)}
  H29:
      {L, n12:ty, n1:var n12, n2:bound n12 T3, n:bound_var n12 T3 n2 n1 |- 
        D5 n12 n2 n1 n : sub (S2 n12) (T4 n12)}
  
  ==================================
  {L |- sa-all S1 ([x]S2 x) T3 ([x]T4 x) (D1 n12) ([w][x][y][z]D5 w y x z) :
    sub (all S1 ([x]S2 x)) (all T3 ([x]T4 x))}
  
  Subgoal trans_and_narrow'.1.2 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.1>> search.
  
  Subgoal trans_and_narrow'.1.2:
  
  Vars: D3:o, D4:o, D5:o, D6:o, D7:o, a1:o, a2:(o) -> (o) -> (o) -> (o) -> o,
          S1:o, S2:(o) -> o, T1:o, T2:(o) -> o, T:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T2 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T2 x))}** =>
              {L |- D2 : sub (all T1 ([x]T2 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 T2 a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}@@
  H3:
      {L |- sa-trans-tvar D3 T (all T1 ([x]T2 x)) D4 D5 D6 D7 :
        sub (all T1 ([x]T2 x)) T}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T2 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T2 n2)}**
  H10:{L |- D3 : ty}
  H11:{L |- T : ty}
  H12:{L |- all T1 ([x]T2 x) : ty}
  H13:{L |- D4 : var (all T1 ([x]T2 x))}
  H14:{L |- D5 : bound (all T1 ([x]T2 x)) D3}
  H15:{L |- D6 : bound_var (all T1 ([x]T2 x)) D3 D5 D4}
  H16:{L |- D7 : sub D3 T}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) T}
  
  Subgoal trans_and_narrow'.1.3 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.2>> cases H13.
  
  Subgoal trans_and_narrow'.1.3:
  
  Vars: D3:o, D4:o, D5:o, D6:o, a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o,
          S2:(o) -> o, T1:o, T2:(o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T2 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T2 x))}** =>
              {L |- D2 : sub (all T1 ([x]T2 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 T2 a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}@@
  H3:
      {L |- sa-refl-tvar D3 (all T1 ([x]T2 x)) D4 D5 D6 :
        sub (all T1 ([x]T2 x)) (all T1 ([x]T2 x))}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T2 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T2 n2)}**
  H10:{L |- D3 : ty}
  H11:{L |- all T1 ([x]T2 x) : ty}
  H12:{L |- D4 : var (all T1 ([x]T2 x))}
  H13:{L |- D5 : bound (all T1 ([x]T2 x)) D3}
  H14:{L |- D6 : bound_var (all T1 ([x]T2 x)) D3 D5 D4}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}
  
  Subgoal trans_and_narrow'.1.4 is:
   exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.3>> cases H12.
  
  Subgoal trans_and_narrow'.1.4:
  
  Vars: a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, T2:
          (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T2 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T2 x))}** =>
              {L |- D2 : sub (all T1 ([x]T2 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 T2 a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}@@
  H3:{L |- sa-top (all T1 ([x]T2 x)) : sub (all T1 ([x]T2 x)) top}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T2 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T2 n2)}**
  H10:{L |- all T1 ([x]T2 x) : ty}
  
  ==================================
  exists D3, {L |- D3 : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.4>> exists sa-top all S1 ([x]S2 x).
  
  Subgoal trans_and_narrow'.1.4:
  
  Vars: a1:o, a2:(o) -> (o) -> (o) -> (o) -> o, S1:o, S2:(o) -> o, T1:o, T2:
          (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- all T1 ([x]T2 x) : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (all T1 ([x]T2 x))}** =>
              {L |- D2 : sub (all T1 ([x]T2 x)) T} =>
                  exists D3, {L |- D3 : sub S T}
  H2:
      {L |- sa-all S1 S2 T1 T2 a1 a2 :
        sub (all S1 ([x]S2 x)) (all T1 ([x]T2 x))}@@
  H3:{L |- sa-top (all T1 ([x]T2 x)) : sub (all T1 ([x]T2 x)) top}
  H4:{L |- S1 : ty}**
  H5:{L, n:ty |- S2 n : ty}**
  H6:{L |- T1 : ty}**
  H7:{L, n1:ty |- T2 n1 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:
      {L, n2:ty, n3:var n2, n4:bound n2 T1, n5:bound_var n2 T1 n4 n3 |- 
        a2 n2 n3 n4 n5 : sub (S2 n2) (T2 n2)}**
  H10:{L |- all T1 ([x]T2 x) : ty}
  
  ==================================
  {L |- sa-top (all S1 ([x]S2 x)) : sub (all S1 ([x]S2 x)) top}
  
  Subgoal trans_and_narrow'.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.1.4>> search.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: a1:o, a2:o, S1:o, S2:o, T1:o, T2:o, D2:o, T:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- arrow T1 T2 : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H3:{L |- D2 : sub (arrow T1 T2) T}
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2>> cases H3.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- arrow T1 T2 : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> cases H1.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  H16:{G |- T1 : ty}*
  H17:{G |- T2 : ty}*
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> apply IH to H16.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  H16:{G |- T1 : ty}*
  H17:{G |- T2 : ty}*
  H18:
      ctx L151820:c.
        forall S, forall T, forall D1, forall D2,
          {L151820 |- D1 : sub S T1} =>
              {L151820 |- D2 : sub T1 T} =>
                  exists D3, {L151820 |- D3 : sub S T}
          /\
          ctx L141719:c.
            forall X, forall M, forall N, forall P, forall D1, forall D2,
              forall DV,
              {L141719 |- X : ty} =>
                  {L141719 |- DV : var X} =>
                      {L141719 |- D1 : sub P T1} =>
                          {L141719 |- [x][y]D2 x y :
                            {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                              exists D4,
                                {L141719 |- [x][y]D4 x y :
                                  {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> cases H18.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  H16:{G |- T1 : ty}*
  H17:{G |- T2 : ty}*
  H19:
      ctx L151820:c.
        forall S, forall T, forall D1, forall D2,
          {L151820 |- D1 : sub S T1} =>
              {L151820 |- D2 : sub T1 T} =>
                  exists D3, {L151820 |- D3 : sub S T}
  H20:
      ctx L141719:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L141719 |- X : ty} =>
              {L141719 |- DV : var X} =>
                  {L141719 |- D1 : sub P T1} =>
                      {L141719 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L141719 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> apply IH to H17.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  H16:{G |- T1 : ty}*
  H17:{G |- T2 : ty}*
  H19:
      ctx L151820:c.
        forall S, forall T, forall D1, forall D2,
          {L151820 |- D1 : sub S T1} =>
              {L151820 |- D2 : sub T1 T} =>
                  exists D3, {L151820 |- D3 : sub S T}
  H20:
      ctx L141719:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L141719 |- X : ty} =>
              {L141719 |- DV : var X} =>
                  {L141719 |- D1 : sub P T1} =>
                      {L141719 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L141719 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H21:
      ctx L222527:c.
        forall S, forall T, forall D1, forall D2,
          {L222527 |- D1 : sub S T2} =>
              {L222527 |- D2 : sub T2 T} =>
                  exists D3, {L222527 |- D3 : sub S T}
          /\
          ctx L212426:c.
            forall X, forall M, forall N, forall P, forall D1, forall D2,
              forall DV,
              {L212426 |- X : ty} =>
                  {L212426 |- DV : var X} =>
                      {L212426 |- D1 : sub P T2} =>
                          {L212426 |- [x][y]D2 x y :
                            {x:bound X T2}{y:bound_var X T2 x DV}sub M N} =>
                              exists D4,
                                {L212426 |- [x][y]D4 x y :
                                  {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> cases H21.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  H16:{G |- T1 : ty}*
  H17:{G |- T2 : ty}*
  H19:
      ctx L151820:c.
        forall S, forall T, forall D1, forall D2,
          {L151820 |- D1 : sub S T1} =>
              {L151820 |- D2 : sub T1 T} =>
                  exists D3, {L151820 |- D3 : sub S T}
  H20:
      ctx L141719:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L141719 |- X : ty} =>
              {L141719 |- DV : var X} =>
                  {L141719 |- D1 : sub P T1} =>
                      {L141719 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L141719 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L222527:c.
        forall S, forall T, forall D1, forall D2,
          {L222527 |- D1 : sub S T2} =>
              {L222527 |- D2 : sub T2 T} =>
                  exists D3, {L222527 |- D3 : sub S T}
  H23:
      ctx L212426:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L212426 |- X : ty} =>
              {L212426 |- DV : var X} =>
                  {L212426 |- D1 : sub P T2} =>
                      {L212426 |- [x][y]D2 x y :
                        {x:bound X T2}{y:bound_var X T2 x DV}sub M N} =>
                          exists D4,
                            {L212426 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> apply H19 to H14 H8.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: D3:o, a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  H16:{G |- T1 : ty}*
  H17:{G |- T2 : ty}*
  H19:
      ctx L151820:c.
        forall S, forall T, forall D1, forall D2,
          {L151820 |- D1 : sub S T1} =>
              {L151820 |- D2 : sub T1 T} =>
                  exists D3, {L151820 |- D3 : sub S T}
  H20:
      ctx L141719:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L141719 |- X : ty} =>
              {L141719 |- DV : var X} =>
                  {L141719 |- D1 : sub P T1} =>
                      {L141719 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L141719 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L222527:c.
        forall S, forall T, forall D1, forall D2,
          {L222527 |- D1 : sub S T2} =>
              {L222527 |- D2 : sub T2 T} =>
                  exists D3, {L222527 |- D3 : sub S T}
  H23:
      ctx L212426:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L212426 |- X : ty} =>
              {L212426 |- DV : var X} =>
                  {L212426 |- D1 : sub P T2} =>
                      {L212426 |- [x][y]D2 x y :
                        {x:bound X T2}{y:bound_var X T2 x DV}sub M N} =>
                          exists D4,
                            {L212426 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D3 : sub T3 S1}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> apply H22 to H9 H15.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: D3:o, a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o, D1:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  H16:{G |- T1 : ty}*
  H17:{G |- T2 : ty}*
  H19:
      ctx L151820:c.
        forall S, forall T, forall D1, forall D2,
          {L151820 |- D1 : sub S T1} =>
              {L151820 |- D2 : sub T1 T} =>
                  exists D3, {L151820 |- D3 : sub S T}
  H20:
      ctx L141719:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L141719 |- X : ty} =>
              {L141719 |- DV : var X} =>
                  {L141719 |- D1 : sub P T1} =>
                      {L141719 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L141719 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L222527:c.
        forall S, forall T, forall D1, forall D2,
          {L222527 |- D1 : sub S T2} =>
              {L222527 |- D2 : sub T2 T} =>
                  exists D3, {L222527 |- D3 : sub S T}
  H23:
      ctx L212426:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L212426 |- X : ty} =>
              {L212426 |- DV : var X} =>
                  {L212426 |- D1 : sub P T2} =>
                      {L212426 |- [x][y]D2 x y :
                        {x:bound X T2}{y:bound_var X T2 x DV}sub M N} =>
                          exists D4,
                            {L212426 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D3 : sub T3 S1}
  H25:{L |- D1 : sub S2 T4}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> exists sa-arrow S1 S2 T3 T4 D3 D1.
  
  Subgoal trans_and_narrow'.2.1:
  
  Vars: D3:o, a3:o, a4:o, T3:o, T4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o, D1:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- T1 : ty}
  H11:{L |- T2 : ty}
  H12:{L |- T3 : ty}
  H13:{L |- T4 : ty}
  H14:{L |- a3 : sub T3 T1}
  H15:{L |- a4 : sub T2 T4}
  H16:{G |- T1 : ty}*
  H17:{G |- T2 : ty}*
  H19:
      ctx L151820:c.
        forall S, forall T, forall D1, forall D2,
          {L151820 |- D1 : sub S T1} =>
              {L151820 |- D2 : sub T1 T} =>
                  exists D3, {L151820 |- D3 : sub S T}
  H20:
      ctx L141719:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L141719 |- X : ty} =>
              {L141719 |- DV : var X} =>
                  {L141719 |- D1 : sub P T1} =>
                      {L141719 |- [x][y]D2 x y :
                        {x:bound X T1}{y:bound_var X T1 x DV}sub M N} =>
                          exists D4,
                            {L141719 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H22:
      ctx L222527:c.
        forall S, forall T, forall D1, forall D2,
          {L222527 |- D1 : sub S T2} =>
              {L222527 |- D2 : sub T2 T} =>
                  exists D3, {L222527 |- D3 : sub S T}
  H23:
      ctx L212426:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L212426 |- X : ty} =>
              {L212426 |- DV : var X} =>
                  {L212426 |- D1 : sub P T2} =>
                      {L212426 |- [x][y]D2 x y :
                        {x:bound X T2}{y:bound_var X T2 x DV}sub M N} =>
                          exists D4,
                            {L212426 |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H24:{L |- D3 : sub T3 S1}
  H25:{L |- D1 : sub S2 T4}
  
  ==================================
  {L |- sa-arrow S1 S2 T3 T4 D3 D1 : sub (arrow S1 S2) (arrow T3 T4)}
  
  Subgoal trans_and_narrow'.2.2 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.1>> search.
  
  Subgoal trans_and_narrow'.2.2:
  
  Vars: U1:o, v:o, a3:o, a4:o, D:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o, T:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- arrow T1 T2 : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- U1 : ty}
  H11:{L |- T : ty}
  H12:{L |- arrow T1 T2 : ty}
  H13:{L |- v : var (arrow T1 T2)}
  H14:{L |- a3 : bound (arrow T1 T2) U1}
  H15:{L |- a4 : bound_var (arrow T1 T2) U1 a3 v}
  H16:{L |- D : sub U1 T}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) T}
  
  Subgoal trans_and_narrow'.2.3 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.2>> cases H13.
  
  Subgoal trans_and_narrow'.2.3:
  
  Vars: U:o, v:o, a3:o, a4:o, a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- arrow T1 T2 : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- U : ty}
  H11:{L |- arrow T1 T2 : ty}
  H12:{L |- v : var (arrow T1 T2)}
  H13:{L |- a3 : bound (arrow T1 T2) U}
  H14:{L |- a4 : bound_var (arrow T1 T2) U a3 v}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) (arrow T1 T2)}
  
  Subgoal trans_and_narrow'.2.4 is:
   exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.3>> cases H12.
  
  Subgoal trans_and_narrow'.2.4:
  
  Vars: a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- arrow T1 T2 : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- arrow T1 T2 : ty}
  
  ==================================
  exists D3, {L |- D3 : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.4>> exists sa-top arrow S1 S2.
  
  Subgoal trans_and_narrow'.2.4:
  
  Vars: a1:o, a2:o, S1:o, S2:o, T1:o, T2:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- arrow T1 T2 : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (arrow T1 T2)}** =>
              {L |- D2 : sub (arrow T1 T2) T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-arrow S1 S2 T1 T2 a1 a2 : sub (arrow S1 S2) (arrow T1 T2)}@@
  H4:{L |- S1 : ty}**
  H5:{L |- S2 : ty}**
  H6:{L |- T1 : ty}**
  H7:{L |- T2 : ty}**
  H8:{L |- a1 : sub T1 S1}**
  H9:{L |- a2 : sub S2 T2}**
  H10:{L |- arrow T1 T2 : ty}
  
  ==================================
  {L |- sa-top (arrow S1 S2) : sub (arrow S1 S2) top}
  
  Subgoal trans_and_narrow'.3 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.2.4>> search.
  
  Subgoal trans_and_narrow'.3:
  
  Vars: U1:o, v:o, a1:o, a2:o, D:o, D2:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-trans-tvar U1 Q S v a1 a2 D : sub S Q}@@
  H3:{L |- D2 : sub Q T}
  H4:{L |- U1 : ty}**
  H5:{L |- Q : ty}**
  H6:{L |- S : ty}**
  H7:{L |- v : var S}**
  H8:{L |- a1 : bound S U1}**
  H9:{L |- a2 : bound_var S U1 a1 v}**
  H10:{L |- D : sub U1 Q}**
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.3>> apply IH1 to H10 H3.
  
  Subgoal trans_and_narrow'.3:
  
  Vars: D3:o, U1:o, v:o, a1:o, a2:o, D:o, D2:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-trans-tvar U1 Q S v a1 a2 D : sub S Q}@@
  H3:{L |- D2 : sub Q T}
  H4:{L |- U1 : ty}**
  H5:{L |- Q : ty}**
  H6:{L |- S : ty}**
  H7:{L |- v : var S}**
  H8:{L |- a1 : bound S U1}**
  H9:{L |- a2 : bound_var S U1 a1 v}**
  H10:{L |- D : sub U1 Q}**
  H11:{L |- D3 : sub U1 T}
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.3>> apply sub__ty to H11.
  
  Subgoal trans_and_narrow'.3:
  
  Vars: D3:o, U1:o, v:o, a1:o, a2:o, D:o, D2:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-trans-tvar U1 Q S v a1 a2 D : sub S Q}@@
  H3:{L |- D2 : sub Q T}
  H4:{L |- U1 : ty}**
  H5:{L |- Q : ty}**
  H6:{L |- S : ty}**
  H7:{L |- v : var S}**
  H8:{L |- a1 : bound S U1}**
  H9:{L |- a2 : bound_var S U1 a1 v}**
  H10:{L |- D : sub U1 Q}**
  H11:{L |- D3 : sub U1 T}
  H12:{L |- U1 : ty} /\ {L |- T : ty}
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.3>> cases H12.
  
  Subgoal trans_and_narrow'.3:
  
  Vars: D3:o, U1:o, v:o, a1:o, a2:o, D:o, D2:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-trans-tvar U1 Q S v a1 a2 D : sub S Q}@@
  H3:{L |- D2 : sub Q T}
  H4:{L |- U1 : ty}**
  H5:{L |- Q : ty}**
  H6:{L |- S : ty}**
  H7:{L |- v : var S}**
  H8:{L |- a1 : bound S U1}**
  H9:{L |- a2 : bound_var S U1 a1 v}**
  H10:{L |- D : sub U1 Q}**
  H11:{L |- D3 : sub U1 T}
  H13:{L |- U1 : ty}
  H14:{L |- T : ty}
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.3>> exists sa-trans-tvar U1 T S v a1 a2 D3.
  
  Subgoal trans_and_narrow'.3:
  
  Vars: D3:o, U1:o, v:o, a1:o, a2:o, D:o, D2:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-trans-tvar U1 Q S v a1 a2 D : sub S Q}@@
  H3:{L |- D2 : sub Q T}
  H4:{L |- U1 : ty}**
  H5:{L |- Q : ty}**
  H6:{L |- S : ty}**
  H7:{L |- v : var S}**
  H8:{L |- a1 : bound S U1}**
  H9:{L |- a2 : bound_var S U1 a1 v}**
  H10:{L |- D : sub U1 Q}**
  H11:{L |- D3 : sub U1 T}
  H13:{L |- U1 : ty}
  H14:{L |- T : ty}
  
  ==================================
  {L |- sa-trans-tvar U1 T S v a1 a2 D3 : sub S T}
  
  Subgoal trans_and_narrow'.4 is:
   exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.3>> search.
  
  Subgoal trans_and_narrow'.4:
  
  Vars: U:o, v:o, a1:o, a2:o, D2:o, T:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-refl-tvar U Q v a1 a2 : sub Q Q}@@
  H3:{L |- D2 : sub Q T}
  H4:{L |- U : ty}**
  H5:{L |- Q : ty}**
  H6:{L |- v : var Q}**
  H7:{L |- a1 : bound Q U}**
  H8:{L |- a2 : bound_var Q U a1 v}**
  
  ==================================
  exists D3, {L |- D3 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.4>> exists D2.
  
  Subgoal trans_and_narrow'.4:
  
  Vars: U:o, v:o, a1:o, a2:o, D2:o, T:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q}** =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-refl-tvar U Q v a1 a2 : sub Q Q}@@
  H3:{L |- D2 : sub Q T}
  H4:{L |- U : ty}**
  H5:{L |- Q : ty}**
  H6:{L |- v : var Q}**
  H7:{L |- a1 : bound Q U}**
  H8:{L |- a2 : bound_var Q U a1 v}**
  
  ==================================
  {L |- D2 : sub Q T}
  
  Subgoal trans_and_narrow'.5 is:
   exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.4>> search.
  
  Subgoal trans_and_narrow'.5:
  
  Vars: D2:o, T:o, S:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- top : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S top}** =>
              {L |- D2 : sub top T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-top S : sub S top}@@
  H3:{L |- D2 : sub top T}
  H4:{L |- S : ty}**
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.5>> cases H3.
  
  Subgoal trans_and_narrow'.5.1:
  
  Vars: U1:o, v:o, a1:o, a2:o, D:o, T:o, S:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- top : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S top}** =>
              {L |- D2 : sub top T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-top S : sub S top}@@
  H4:{L |- S : ty}**
  H5:{L |- U1 : ty}
  H6:{L |- T : ty}
  H7:{L |- top : ty}
  H8:{L |- v : var top}
  H9:{L |- a1 : bound top U1}
  H10:{L |- a2 : bound_var top U1 a1 v}
  H11:{L |- D : sub U1 T}
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow'.5.2 is:
   exists D3, {L |- D3 : sub S top}
  
  Subgoal trans_and_narrow'.5.3 is:
   exists D3, {L |- D3 : sub S top}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.5.1>> cases H8.
  
  Subgoal trans_and_narrow'.5.2:
  
  Vars: U:o, v:o, a1:o, a2:o, S:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- top : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S top}** =>
              {L |- D2 : sub top T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-top S : sub S top}@@
  H4:{L |- S : ty}**
  H5:{L |- U : ty}
  H6:{L |- top : ty}
  H7:{L |- v : var top}
  H8:{L |- a1 : bound top U}
  H9:{L |- a2 : bound_var top U a1 v}
  
  ==================================
  exists D3, {L |- D3 : sub S top}
  
  Subgoal trans_and_narrow'.5.3 is:
   exists D3, {L |- D3 : sub S top}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.5.2>> cases H7.
  
  Subgoal trans_and_narrow'.5.3:
  
  Vars: S:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- top : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S top}** =>
              {L |- D2 : sub top T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-top S : sub S top}@@
  H4:{L |- S : ty}**
  H5:{L |- top : ty}
  
  ==================================
  exists D3, {L |- D3 : sub S top}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.5.3>> exists sa-top S.
  
  Subgoal trans_and_narrow'.5.3:
  
  Vars: S:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- top : ty}@
  IH1:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S top}** =>
              {L |- D2 : sub top T} => exists D3, {L |- D3 : sub S T}
  H2:{L |- sa-top S : sub S top}@@
  H4:{L |- S : ty}**
  H5:{L |- top : ty}
  
  ==================================
  {L |- sa-top S : sub S top}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall S, forall T, forall D1, forall D2,
       {L |- D1 : sub S Q} =>
           {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
       /\
       ctx L:c.
         forall X, forall M, forall N, forall P, forall D1, forall D2,
           forall DV,
           {L |- X : ty} =>
               {L |- DV : var X} =>
                   {L |- D1 : sub P Q} =>
                       {L |- [x][y]D2 x y :
                         {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                           exists D4,
                             {L |- [x][y]D4 x y :
                               {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'.5.3>> search.
  
  Subgoal trans_and_narrow':
  
  Vars: Q:o
  Contexts: G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  
  ==================================
  ctx L:c.
    forall S, forall T, forall D1, forall D2,
      {L |- D1 : sub S Q} =>
          {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
      /\
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> split.
  
  Subgoal trans_and_narrow':
  
  Vars: Q:o
  Contexts: G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  
  ==================================
  ctx L:c.
    forall S, forall T, forall D1, forall D2,
      {L |- D1 : sub S Q} =>
          {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall X, forall M, forall N, forall P, forall D1, forall D2, forall DV,
       {L |- X : ty} =>
           {L |- DV : var X} =>
               {L |- D1 : sub P Q} =>
                   {L |- [x][y]D2 x y :
                     {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                       exists D4,
                         {L |- [x][y]D4 x y :
                           {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> intros.
  
  Subgoal trans_and_narrow':
  
  Vars: D2:o, D1:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H3:{L |- D1 : sub S Q}
  H4:{L |- D2 : sub Q T}
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall X, forall M, forall N, forall P, forall D1, forall D2, forall DV,
       {L |- X : ty} =>
           {L |- DV : var X} =>
               {L |- D1 : sub P Q} =>
                   {L |- [x][y]D2 x y :
                     {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                       exists D4,
                         {L |- [x][y]D4 x y :
                           {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> apply H2 to H3 H4.
  
  Subgoal trans_and_narrow':
  
  Vars: D3:o, D2:o, D1:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H3:{L |- D1 : sub S Q}
  H4:{L |- D2 : sub Q T}
  H5:{L |- D3 : sub S T}
  
  ==================================
  exists D3, {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall X, forall M, forall N, forall P, forall D1, forall D2, forall DV,
       {L |- X : ty} =>
           {L |- DV : var X} =>
               {L |- D1 : sub P Q} =>
                   {L |- [x][y]D2 x y :
                     {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                       exists D4,
                         {L |- [x][y]D4 x y :
                           {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> exists D3.
  
  Subgoal trans_and_narrow':
  
  Vars: D3:o, D2:o, D1:o, T:o, S:o, Q:o
  Contexts: L{}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  H3:{L |- D1 : sub S Q}
  H4:{L |- D2 : sub Q T}
  H5:{L |- D3 : sub S T}
  
  ==================================
  {L |- D3 : sub S T}
  
  Subgoal trans_and_narrow' is:
   ctx L:c.
     forall X, forall M, forall N, forall P, forall D1, forall D2, forall DV,
       {L |- X : ty} =>
           {L |- DV : var X} =>
               {L |- D1 : sub P Q} =>
                   {L |- [x][y]D2 x y :
                     {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                       exists D4,
                         {L |- [x][y]D4 x y :
                           {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> search.
  
  Subgoal trans_and_narrow':
  
  Vars: Q:o
  Contexts: G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  
  ==================================
  ctx L:c.
    forall X, forall M, forall N, forall P, forall D1, forall D2, forall DV,
      {L |- X : ty} =>
          {L |- DV : var X} =>
              {L |- D1 : sub P Q} =>
                  {L |- [x][y]D2 x y :
                    {x:bound X Q}{y:bound_var X Q x DV}sub M N} =>
                      exists D4,
                        {L |- [x][y]D4 x y :
                          {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> induction on 4.
  
  Subgoal trans_and_narrow':
  
  Vars: Q:o
  Contexts: G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  ==================================
  ctx L:c.
    forall X, forall M, forall N, forall P, forall D1, forall D2, forall DV,
      {L |- X : ty} =>
          {L |- DV : var X} =>
              {L |- D1 : sub P Q} =>
                  {L |- [x][y]D2 x y :
                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}@@@ =>
                      exists D4,
                        {L |- [x][y]D4 x y :
                          {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> intros.
  
  Subgoal trans_and_narrow':
  
  Vars: DV:o, D2:(o) -> (o) -> o, D1:o, P:o, N:o, M:o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:{L, n:bound X Q, n1:bound_var X Q n DV |- D2 n n1 : sub M N}@@@
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  trans_and_narrow'>> cases H6.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: a1:(o) -> (o) -> o, a2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:
          o, M2:(o) -> o, N1:o, N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> apply IH1 to H3 H4 H5 H11 with X = X, M = N1, N = M1, P = P, D1 = D1, D2 =
      [x][y]a1 y x.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:
          (o) ->
            (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o,
          a1:(o) -> (o) -> o, a2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o,
          M1:o, M2:(o) -> o, N1:o, N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:
      {L, n8:bound X P, n9:bound_var X P n8 DV |- 
        D4 n7 n6 n5 n4 n3 n2 n1 n n8 n9 : sub N1 M1}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> prune H13.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> assert {L,n:ty,n2:var n,n1:bound n N1,n3:bound_var n N1 n1 n2,n4:bound X Q,
           n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub M2 n N2 n}***.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q, n5:
    bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> ctxpermute H12 to L,n4:ty,n5:var n4,n6:bound n4 N1,n7:bound_var n4 N1 n6 n5,
      n:bound X Q,n1:bound_var X Q n DV.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n4:ty, n5:var n4, n6:bound n4 N1, n7:bound_var n4 N1 n6 n5, n:
        bound X Q, n1:bound_var X Q n DV |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q, n5:
    bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> search.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> assert {L,n:ty,n2:var n,n1:bound n N1,n3:bound_var n N1 n1 n2 |- D1 :
           sub P Q}.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H5 with ty.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H15 with var n10.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  H16:{L, n10:ty, n11:var n10 |- D1 : sub P Q}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H9.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  H16:{L, n10:ty, n11:var n10 |- D1 : sub P Q}
  H17:{L, n:bound X Q |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H17.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  H16:{L, n10:ty, n11:var n10 |- D1 : sub P Q}
  H17:{L, n:bound X Q |- N1 : ty}***
  H18:{L |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H18 with ty.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:
              wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  H16:{L, n10:ty, n11:var n10 |- D1 : sub P Q}
  H17:{L, n:bound X Q |- N1 : ty}***
  H18:{L |- N1 : ty}***
  H19:{L, n12:ty |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H19 with var n12.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  H16:{L, n10:ty, n11:var n10 |- D1 : sub P Q}
  H17:{L, n:bound X Q |- N1 : ty}***
  H18:{L |- N1 : ty}***
  H19:{L, n12:ty |- N1 : ty}***
  H20:{L, n12:ty, n13:var n12 |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H16 with bound n10 N1.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:
              c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  H16:{L, n10:ty, n11:var n10 |- D1 : sub P Q}
  H17:{L, n:bound X Q |- N1 : ty}***
  H18:{L |- N1 : ty}***
  H19:{L, n12:ty |- N1 : ty}***
  H20:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H21:{L, n10:ty, n11:var n10, n14:bound n10 N1 |- D1 : sub P Q}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H20 with bound n12 N1.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o,
              n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n15, n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1,
              n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  H16:{L, n10:ty, n11:var n10 |- D1 : sub P Q}
  H17:{L, n:bound X Q |- N1 : ty}***
  H18:{L |- N1 : ty}***
  H19:{L, n12:ty |- N1 : ty}***
  H20:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H21:{L, n10:ty, n11:var n10, n14:bound n10 N1 |- D1 : sub P Q}
  H22:{L, n12:ty, n13:var n12, n15:bound n12 N1 |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H21 with bound_var n10 N1 n14 n11.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n16:o, n15:o, n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o,
              n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n16, n15, n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3,
              n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:{L, n10:ty |- D1 : sub P Q}
  H16:{L, n10:ty, n11:var n10 |- D1 : sub P Q}
  H17:{L, n:bound X Q |- N1 : ty}***
  H18:{L |- N1 : ty}***
  H19:{L, n12:ty |- N1 : ty}***
  H20:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H21:{L, n10:ty, n11:var n10, n14:bound n10 N1 |- D1 : sub P Q}
  H22:{L, n12:ty, n13:var n12, n15:bound n12 N1 |- N1 : ty}***
  H23:
      {L, n10:ty, n11:var n10, n14:bound n10 N1, n16:bound_var n10 N1 n14 n11
        |- D1 : sub P Q}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> search.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> assert {L,n:ty,n2:var n,n1:bound n N1,n3:bound_var n N1 n1 n2 |- X : ty}.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H3 with ty.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H16 with var n10.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  H17:{L, n10:ty, n11:var n10 |- X : ty}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H9.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  H17:{L, n10:ty, n11:var n10 |- X : ty}
  H18:{L, n:bound X Q |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H18.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  H17:{L, n10:ty, n11:var n10 |- X : ty}
  H18:{L, n:bound X Q |- N1 : ty}***
  H19:{L |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H19 with ty.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:
              wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  H17:{L, n10:ty, n11:var n10 |- X : ty}
  H18:{L, n:bound X Q |- N1 : ty}***
  H19:{L |- N1 : ty}***
  H20:{L, n12:ty |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H20 with var n12.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  H17:{L, n10:ty, n11:var n10 |- X : ty}
  H18:{L, n:bound X Q |- N1 : ty}***
  H19:{L |- N1 : ty}***
  H20:{L, n12:ty |- N1 : ty}***
  H21:{L, n12:ty, n13:var n12 |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H21 with bound n12 N1.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:
              c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  H17:{L, n10:ty, n11:var n10 |- X : ty}
  H18:{L, n:bound X Q |- N1 : ty}***
  H19:{L |- N1 : ty}***
  H20:{L, n12:ty |- N1 : ty}***
  H21:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H22:{L, n12:ty, n13:var n12, n14:bound n12 N1 |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H17 with bound n10 N1.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o,
              n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n15, n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1,
              n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  H17:{L, n10:ty, n11:var n10 |- X : ty}
  H18:{L, n:bound X Q |- N1 : ty}***
  H19:{L |- N1 : ty}***
  H20:{L, n12:ty |- N1 : ty}***
  H21:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H22:{L, n12:ty, n13:var n12, n14:bound n12 N1 |- N1 : ty}***
  H23:{L, n10:ty, n11:var n10, n15:bound n10 N1 |- X : ty}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H23 with bound_var n10 N1 n15 n11.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n16:o, n15:o, n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o,
              n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n16, n15, n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3,
              n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n10:ty |- X : ty}
  H17:{L, n10:ty, n11:var n10 |- X : ty}
  H18:{L, n:bound X Q |- N1 : ty}***
  H19:{L |- N1 : ty}***
  H20:{L, n12:ty |- N1 : ty}***
  H21:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H22:{L, n12:ty, n13:var n12, n14:bound n12 N1 |- N1 : ty}***
  H23:{L, n10:ty, n11:var n10, n15:bound n10 N1 |- X : ty}
  H24:
      {L, n10:ty, n11:var n10, n15:bound n10 N1, n16:bound_var n10 N1 n15 n11
        |- X : ty}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> search.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> assert {L,n:ty,n2:var n,n1:bound n N1,n3:bound_var n N1 n1 n2 |- DV : var X}.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H4 with ty.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H17 with var n10.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  H18:{L, n10:ty, n11:var n10 |- DV : var X}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H9.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  H18:{L, n10:ty, n11:var n10 |- DV : var X}
  H19:{L, n:bound X Q |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H19.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  H18:{L, n10:ty, n11:var n10 |- DV : var X}
  H19:{L, n:bound X Q |- N1 : ty}***
  H20:{L |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H20 with ty.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:
              o, n1:o, n:o
  Contexts: L{n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:
              wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  H18:{L, n10:ty, n11:var n10 |- DV : var X}
  H19:{L, n:bound X Q |- N1 : ty}***
  H20:{L |- N1 : ty}***
  H21:{L, n12:ty |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H21 with var n12.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[],
              G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  H18:{L, n10:ty, n11:var n10 |- DV : var X}
  H19:{L, n:bound X Q |- N1 : ty}***
  H20:{L |- N1 : ty}***
  H21:{L, n12:ty |- N1 : ty}***
  H22:{L, n12:ty, n13:var n12 |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H22 with bound n12 N1.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4
              :o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:
              c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  H18:{L, n10:ty, n11:var n10 |- DV : var X}
  H19:{L, n:bound X Q |- N1 : ty}***
  H20:{L |- N1 : ty}***
  H21:{L, n12:ty |- N1 : ty}***
  H22:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H23:{L, n12:ty, n13:var n12, n14:bound n12 N1 |- N1 : ty}***
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H18 with bound n10 N1.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o,
              n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n15, n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1,
              n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  H18:{L, n10:ty, n11:var n10 |- DV : var X}
  H19:{L, n:bound X Q |- N1 : ty}***
  H20:{L |- N1 : ty}***
  H21:{L, n12:ty |- N1 : ty}***
  H22:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H23:{L, n12:ty, n13:var n12, n14:bound n12 N1 |- N1 : ty}***
  H24:{L, n10:ty, n11:var n10, n15:bound n10 N1 |- DV : var X}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> weaken H24 with bound_var n10 N1 n15 n11.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n16:o, n15:o, n14:o, n13:o, n12:o, n11:o, n10:o, n9:o, n8:o, n7:o,
              n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n16, n15, n14, n13, n12, n11, n10, n9, n8, n7, n6, n5, n4, n3,
              n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n10:ty |- DV : var X}
  H18:{L, n10:ty, n11:var n10 |- DV : var X}
  H19:{L, n:bound X Q |- N1 : ty}***
  H20:{L |- N1 : ty}***
  H21:{L, n12:ty |- N1 : ty}***
  H22:{L, n12:ty, n13:var n12 |- N1 : ty}***
  H23:{L, n12:ty, n13:var n12, n14:bound n12 N1 |- N1 : ty}***
  H24:{L, n10:ty, n11:var n10, n15:bound n10 N1 |- DV : var X}
  H25:
      {L, n10:ty, n11:var n10, n15:bound n10 N1, n16:bound_var n10 N1 n15 n11
        |- DV : var X}
  
  ==================================
  {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  Subgoal trans_and_narrow'.1 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P
         }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> search.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> apply IH1 to H16 H17 H15 H14 with (L = L,n:ty,n2:var n,n1:bound n N1,
      n3:bound_var n N1 n1 n2), X = X, M = M2 n, N = N2 n, P = P, D1 = D1, D2 =
      [x][y]a2 y x n n2 n1 n3, DV = DV.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:
          (o) ->
            (o) ->
              (o) ->
                (o) ->
                  (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o,
          D1:o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- 
        D2 n9 n8 n7 n6 n5 n4 n3 n2 n1 n n10 n11 : sub (M2 n) (N2 n)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> prune H18.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> ctxpermute H18 to L,n10:bound X P,n11:bound_var X P n10 DV,n:ty,n2:var n,
      n1:bound n N1,n3:bound_var n N1 n1 n2.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> apply sub__ty to H13 with (L = L,n1:bound X P,n:bound_var X P n1 DV).
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H20:
      {L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty} /\
          {L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> cases H20.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o,
              n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> apply sub__ty to H19 with (L = L,n14:bound X P,n15:bound_var X P n14 DV,n:ty,
      n2:var n,n1:bound n N1,n3:bound_var n N1 n1 n2), D =
      D2 n3 n2 n1 n n14 n15, U1 = M2 n, U2 = N2 n.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H23:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty} /\
          {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
            bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> cases H23.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H24:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty}
  H25:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H24.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H24:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty}
  H25:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  H26:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- M2 n : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H26.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H24:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty}
  H25:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  H26:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- M2 n : ty}
  H27:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- M2 n : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H27.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H24:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty}
  H25:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  H26:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- M2 n : ty}
  H27:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- M2 n : ty}
  H28:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty |- M2 n : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H25.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H24:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty}
  H25:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  H26:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- M2 n : ty}
  H27:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- M2 n : ty}
  H28:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty |- M2 n : ty}
  H29:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- N2 n : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H29.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H24:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty}
  H25:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  H26:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- M2 n : ty}
  H27:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- M2 n : ty}
  H28:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty |- M2 n : ty}
  H29:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- N2 n : ty}
  H30:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- N2 n : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> strengthen H30.
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H24:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty}
  H25:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  H26:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- M2 n : ty}
  H27:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- M2 n : ty}
  H28:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty |- M2 n : ty}
  H29:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- N2 n : ty}
  H30:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- N2 n : ty}
  H31:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty |- N2 n : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P
        }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> exists [w]
           [x]
             sa-all M1 ([z]M2 z) N1 ([z]N2 z) D4 w x
               ([x1][x2][x3][x4]D2 x4 x2 x3 x1 w x).
  
  Subgoal trans_and_narrow'.1:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:o, M2:(o) -> o, N1:o,
          N2:(o) -> o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1
          :o, P:o, X:o, Q:o
  Nominals: n15:o, n14:o, n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n5:o, n4:o, n3:
              o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-all M1 ([z3]M2 z3) N1 ([z3]N2 z3) (a1 n1 n) (a2 n1 n) :
        sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV, n2:ty |- M2 n2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV, n3:ty |- N2 n3 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV, n4:ty, n5:var n4, n6:bound n4 N1,
        n7:bound_var n4 N1 n6 n5 |- a2 n1 n n4 n5 n6 n7 :
        sub (M2 n4) (N2 n4)}***
  H13:{L, n8:bound X P, n9:bound_var X P n8 DV |- D4 n8 n9 : sub N1 M1}
  H14:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n4:bound X Q,
        n5:bound_var X Q n4 DV |- a2 n5 n4 n n2 n1 n3 : sub (M2 n) (N2 n)}***
  H15:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- D1 :
        sub P Q}
  H16:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- X : ty}
  H17:{L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2 |- DV : var X}
  H18:
      {L, n:ty, n2:var n, n1:bound n N1, n3:bound_var n N1 n1 n2, n10:
        bound X P, n11:bound_var X P n10 DV |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H19:
      {L, n10:bound X P, n11:bound_var X P n10 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- D2 n3 n2 n1 n n10 n11 :
        sub (M2 n) (N2 n)}
  H21:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H22:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H24:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- M2 n : ty}
  H25:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1, n3:bound_var n N1 n1 n2 |- N2 n : ty}
  H26:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- M2 n : ty}
  H27:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- M2 n : ty}
  H28:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty |- M2 n : ty}
  H29:
      {L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n, n1:
        bound n N1 |- N2 n : ty}
  H30:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty, n2:var n |- N2 n : ty}
  H31:{L, n14:bound X P, n15:bound_var X P n14 DV, n:ty |- N2 n : ty}
  
  ==================================
  {L |- 
    [x
      ][y
         ]sa-all M1 ([z]M2 z) N1 ([z]N2 z) (D4 x y)
            ([x1][x2][x3][x4]D2 x4 x2 x3 x1 x y)
    :
    {x:bound X P
      }{y:bound_var X P x DV}sub (all M1 ([x]M2 x)) (all N1 ([x]N2 x))}
  
  Subgoal trans_and_narrow'.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.1>> search.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o, N1:o, N2:o, DV:o,
          D1:o, P:o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> apply IH1 to H3 H4 H5 H11 with X = X, M = N1, N = M1, P = P, DV = DV, D1 =
      D1, D2 = [x][y]a1 y x.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> o, M1:o, M2:o, N1:o, N2:o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n1 n n2 n3 : sub N1 M1}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> prune H13.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o,
          N1:o, N2:o, DV:o, D1:o, P:o, X:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n2 n3 : sub N1 M1}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> apply IH1 to H3 H4 H5 H12 with X = X, M = M2, N = N2, P = P, DV = DV, D1 =
      D1, D2 = [x][y]a2 y x.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o,
          N1:o, N2:o, DV:o, D2:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D1:
          o, P:o, X:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n2 n3 : sub N1 M1}
  H14:
      {L, n4:bound X P, n5:bound_var X P n4 DV |- D2 n3 n2 n1 n n4 n5 :
        sub M2 N2}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> prune H14.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o,
          N1:o, N2:o, DV:o, D2:(o) -> (o) -> o, D1:o, P:o, X:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n2 n3 : sub N1 M1}
  H14:{L, n4:bound X P, n5:bound_var X P n4 DV |- D2 n4 n5 : sub M2 N2}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> apply sub__ty to H13 with (L = L,n1:bound X P,n:bound_var X P n1 DV).
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o,
          N1:o, N2:o, DV:o, D2:(o) -> (o) -> o, D1:o, P:o, X:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n2 n3 : sub N1 M1}
  H14:{L, n4:bound X P, n5:bound_var X P n4 DV |- D2 n4 n5 : sub M2 N2}
  H15:
      {L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty} /\
          {L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> cases H15.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o,
          N1:o, N2:o, DV:o, D2:(o) -> (o) -> o, D1:o, P:o, X:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n2 n3 : sub N1 M1}
  H14:{L, n4:bound X P, n5:bound_var X P n4 DV |- D2 n4 n5 : sub M2 N2}
  H16:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H17:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> apply sub__ty to H14 with (L = L,n1:bound X P,n:bound_var X P n1 DV).
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o,
          N1:o, N2:o, DV:o, D2:(o) -> (o) -> o, D1:o, P:o, X:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n2 n3 : sub N1 M1}
  H14:{L, n4:bound X P, n5:bound_var X P n4 DV |- D2 n4 n5 : sub M2 N2}
  H16:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H17:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H18:
      {L, n1:bound X P, n:bound_var X P n1 DV |- M2 : ty} /\
          {L, n1:bound X P, n:bound_var X P n1 DV |- N2 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> cases H18.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o,
          N1:o, N2:o, DV:o, D2:(o) -> (o) -> o, D1:o, P:o, X:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n2 n3 : sub N1 M1}
  H14:{L, n4:bound X P, n5:bound_var X P n4 DV |- D2 n4 n5 : sub M2 N2}
  H16:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H17:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H19:{L, n1:bound X P, n:bound_var X P n1 DV |- M2 : ty}
  H20:{L, n1:bound X P, n:bound_var X P n1 DV |- N2 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> exists [x][y]sa-arrow M1 M2 N1 N2 D4 x y D2 x y.
  
  Subgoal trans_and_narrow'.2:
  
  Vars: D4:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:(o) -> (o) -> o, M1:o, M2:o,
          N1:o, N2:o, DV:o, D2:(o) -> (o) -> o, D1:o, P:o, X:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-arrow M1 M2 N1 N2 (a1 n1 n) (a2 n1 n) :
        sub (arrow M1 M2) (arrow N1 N2)}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M1 : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- M2 : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- N1 : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- N2 : ty}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : sub N1 M1}***
  H12:{L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n : sub M2 N2}***
  H13:{L, n2:bound X P, n3:bound_var X P n2 DV |- D4 n2 n3 : sub N1 M1}
  H14:{L, n4:bound X P, n5:bound_var X P n4 DV |- D2 n4 n5 : sub M2 N2}
  H16:{L, n1:bound X P, n:bound_var X P n1 DV |- N1 : ty}
  H17:{L, n1:bound X P, n:bound_var X P n1 DV |- M1 : ty}
  H19:{L, n1:bound X P, n:bound_var X P n1 DV |- M2 : ty}
  H20:{L, n1:bound X P, n:bound_var X P n1 DV |- N2 : ty}
  
  ==================================
  {L |- [x][y]sa-arrow M1 M2 N1 N2 (D4 x y) (D2 x y) :
    {x:bound X P}{y:bound_var X P x DV}sub (arrow M1 M2) (arrow N1 N2)}
  
  Subgoal trans_and_narrow'.3 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.2>> search.
  
  Subgoal trans_and_narrow'.3:
  
  Vars: U1:(o) -> (o) -> o, v:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, X:o, Q
          :o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-trans-tvar (U1 n1 n) N M (v n1 n) (a1 n1 n) (a2 n1 n) (D n1 n) :
        sub M N}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- U1 n1 n : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- N : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- M : ty}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- v n1 n : var M}***
  H11:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : bound M (U1 n1 n)}***
  H12:
      {L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n :
        bound_var M (U1 n1 n) (a1 n1 n) (v n1 n)}***
  H13:{L, n:bound X Q, n1:bound_var X Q n DV |- D n1 n : sub (U1 n1 n) N}***
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M N}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3>> cases H11.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: v:(o) -> (o) -> o, a2:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P
          :o, N:o, M:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M (v n1 n) n (a2 n1 n) (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- v n1 n : var M}***
  H12:
      {L, n:bound M Q, n1:bound_var M Q n DV |- a2 n1 n :
        bound_var M Q n (v n1 n)}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> cases H12.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> apply IH1 to H3 H4 H5 H13 with M = Q, N = N, D1 = D1, D2 = [x][y]D y x.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N
          :o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n1 n n2 n3 : sub Q N}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> prune H14.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> assert {L,n:bound M P,n1:bound_var M P n DV |- D1 : sub P Q}.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> apply sub__ty to H5.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L |- P : ty} /\ {L |- Q : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> cases H15.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> apply sub__ty to H6 with (L = L,n1:bound M Q,n:bound_var M Q n1 DV).
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H18:
      {L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty} /\
          {L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> cases H18.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> strengthen H19.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> strengthen H21.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  H22:{L |- M : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> strengthen H10.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  H22:{L |- M : ty}
  H23:{L, n:bound M Q |- DV : var M}***
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> strengthen H23.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  H22:{L |- M : ty}
  H23:{L, n:bound M Q |- DV : var M}***
  H24:{L |- DV : var M}***
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H24 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  H22:{L |- M : ty}
  H23:{L, n:bound M Q |- DV : var M}***
  H24:{L |- DV : var M}***
  H25:{L, n4:bound M P |- DV : var M}***
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H22 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  H22:{L |- M : ty}
  H23:{L, n:bound M Q |- DV : var M}***
  H24:{L |- DV : var M}***
  H25:{L, n4:bound M P |- DV : var M}***
  H26:{L, n5:bound M P |- M : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H16 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  H22:{L |- M : ty}
  H23:{L, n:bound M Q |- DV : var M}***
  H24:{L |- DV : var M}***
  H25:{L, n4:bound M P |- DV : var M}***
  H26:{L, n5:bound M P |- M : ty}
  H27:{L, n6:bound M P |- P : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H5 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  H22:{L |- M : ty}
  H23:{L, n:bound M Q |- DV : var M}***
  H24:{L |- DV : var M}***
  H25:{L, n4:bound M P |- DV : var M}***
  H26:{L, n5:bound M P |- M : ty}
  H27:{L, n6:bound M P |- P : ty}
  H28:{L, n7:bound M P |- D1 : sub P Q}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H28 with bound_var M P n7 DV.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n8:o, n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n8, n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H16:{L |- P : ty}
  H17:{L |- Q : ty}
  H19:{L, n1:bound M Q, n:bound_var M Q n1 DV |- M : ty}
  H20:{L, n1:bound M Q, n:bound_var M Q n1 DV |- N : ty}
  H21:{L, n1:bound M Q |- M : ty}
  H22:{L |- M : ty}
  H23:{L, n:bound M Q |- DV : var M}***
  H24:{L |- DV : var M}***
  H25:{L, n4:bound M P |- DV : var M}***
  H26:{L, n5:bound M P |- M : ty}
  H27:{L, n6:bound M P |- P : ty}
  H28:{L, n7:bound M P |- D1 : sub P Q}
  H29:{L, n7:bound M P, n8:bound_var M P n7 DV |- D1 : sub P Q}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> search.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> apply H2 to H15 H14 with (L = L,n:bound M P,n1:bound_var M P n DV), S = P, T
      = N, D1 = D1, D2 = D4 n n1.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> (o) -> (o) -> o, D4:(o) -> (o) -> o, D:
          (o) -> (o) -> o, DV:o, D1:o, P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n3 n2 n1 n : sub P N}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> prune H16.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> apply sub__ty to H16 with (L = L,n1:bound M P,n:bound_var M P n1 DV).
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H17:
      {L, n1:bound M P, n:bound_var M P n1 DV |- P : ty} /\
          {L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> cases H17.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> assert {L,n:bound M P,n1:bound_var M P n DV |- M : ty}.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> apply sub__ty to H5.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L |- P : ty} /\ {L |- Q : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> cases H20.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H21:{L |- P : ty}
  H22:{L |- Q : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H21 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H21:{L |- P : ty}
  H22:{L |- Q : ty}
  H23:{L, n4:bound M P |- P : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H4 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H21:{L |- P : ty}
  H22:{L |- Q : ty}
  H23:{L, n4:bound M P |- P : ty}
  H24:{L, n5:bound M P |- DV : var M}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H3 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H21:{L |- P : ty}
  H22:{L |- Q : ty}
  H23:{L, n4:bound M P |- P : ty}
  H24:{L, n5:bound M P |- DV : var M}
  H25:{L, n6:bound M P |- M : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H25 with bound_var M P n6 DV.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H21:{L |- P : ty}
  H22:{L |- Q : ty}
  H23:{L, n4:bound M P |- P : ty}
  H24:{L, n5:bound M P |- DV : var M}
  H25:{L, n6:bound M P |- M : ty}
  H26:{L, n6:bound M P, n7:bound_var M P n6 DV |- M : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> search.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> assert {L,n:bound M P,n1:bound_var M P n DV |- DV : var M}.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> apply sub__ty to H5.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  H21:{L |- P : ty} /\ {L |- Q : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> cases H21.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  H22:{L |- P : ty}
  H23:{L |- Q : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H22 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  H22:{L |- P : ty}
  H23:{L |- Q : ty}
  H24:{L, n4:bound M P |- P : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H3 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  H22:{L |- P : ty}
  H23:{L |- Q : ty}
  H24:{L, n4:bound M P |- P : ty}
  H25:{L, n5:bound M P |- M : ty}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H4 with bound M P.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  H22:{L |- P : ty}
  H23:{L |- Q : ty}
  H24:{L, n4:bound M P |- P : ty}
  H25:{L, n5:bound M P |- M : ty}
  H26:{L, n6:bound M P |- DV : var M}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> weaken H26 with bound_var M P n6 DV.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  H22:{L |- P : ty}
  H23:{L |- Q : ty}
  H24:{L, n4:bound M P |- P : ty}
  H25:{L, n5:bound M P |- M : ty}
  H26:{L, n6:bound M P |- DV : var M}
  H27:{L, n6:bound M P, n7:bound_var M P n6 DV |- DV : var M}
  
  ==================================
  {L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  Subgoal trans_and_narrow'.3.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> search.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  H21:{L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> exists [x][y]sa-trans-tvar P N M DV x y D3 y x.
  
  Subgoal trans_and_narrow'.3.1:
  
  Vars: D3:(o) -> (o) -> o, D4:(o) -> (o) -> o, D:(o) -> (o) -> o, DV:o, D1:o,
          P:o, N:o, M:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- M : ty}
  H4:{L |- DV : var M}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound M Q, n1:bound_var M Q n DV |- 
        sa-trans-tvar Q N M DV n n1 (D n1 n) : sub M N}@@@
  H7:{L, n:bound M Q, n1:bound_var M Q n DV |- Q : ty}***
  H8:{L, n:bound M Q, n1:bound_var M Q n DV |- N : ty}***
  H9:{L, n:bound M Q, n1:bound_var M Q n DV |- M : ty}***
  H10:{L, n:bound M Q, n1:bound_var M Q n DV |- DV : var M}***
  H13:{L, n:bound M Q, n1:bound_var M Q n DV |- D n1 n : sub Q N}***
  H14:{L, n2:bound M P, n3:bound_var M P n2 DV |- D4 n2 n3 : sub Q N}
  H15:{L, n:bound M P, n1:bound_var M P n DV |- D1 : sub P Q}
  H16:{L, n:bound M P, n1:bound_var M P n DV |- D3 n1 n : sub P N}
  H18:{L, n1:bound M P, n:bound_var M P n1 DV |- P : ty}
  H19:{L, n1:bound M P, n:bound_var M P n1 DV |- N : ty}
  H20:{L, n:bound M P, n1:bound_var M P n DV |- M : ty}
  H21:{L, n:bound M P, n1:bound_var M P n DV |- DV : var M}
  
  ==================================
  {L |- [x][y]sa-trans-tvar P N M DV x y (D3 y x) :
    {x:bound M P}{y:bound_var M P x DV}sub M N}
  
  Subgoal trans_and_narrow'.3.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.1>> search.
  
  Subgoal trans_and_narrow'.3.2:
  
  Vars: U2:(o) -> (o) -> (o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> o, P:
          (o) -> (o) -> (o) -> (o) -> o, N:(o) -> (o) -> (o) -> (o) -> o, X:
          (o) -> (o) -> (o) -> (o) -> o, Q:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U2 n2 n3 n4 n5), n5:
              bound_var n2 (U2 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-trans-tvar (U2 n2 n3 n4 n5) (N n2 n3 n4 n5) n2 (v n2 n3 n4 n5 n1 n)
          n4 (a2 n2 n3 n4 n5 n1 n) (D n2 n3 n4 n5 n1 n)
        : sub n2 (N n2 n3 n4 n5)}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        N n2 n3 n4 n5 : ty}***
  H9:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H10:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        v n2 n3 n4 n5 n1 n : var n2}***
  H12:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        a2 n2 n3 n4 n5 n1 n :
        bound_var n2 (U2 n2 n3 n4 n5) n4 (v n2 n3 n4 n5 n1 n)}***
  H13:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        D n2 n3 n4 n5 n1 n : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.2>> apply IH1 to H3 H4 H5 H13 with X = X n2 n3 n4 n5, M = U2 n2 n3 n4 n5, N =
      N n2 n3 n4 n5, P = P n2 n3 n4 n5, D1 = D1 n2 n3 n4 n5, D2 =
      [x][y]D n2 n3 n4 n5 y x, DV = DV n2 n3 n4 n5.
  
  Subgoal trans_and_narrow'.3.2:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, U2:
          (o) -> (o) -> (o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> o, P:
          (o) -> (o) -> (o) -> (o) -> o, N:(o) -> (o) -> (o) -> (o) -> o, X:
          (o) -> (o) -> (o) -> (o) -> o, Q:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U2 n2 n3 n4 n5),
              n5:bound_var n2 (U2 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-trans-tvar (U2 n2 n3 n4 n5) (N n2 n3 n4 n5) n2 (v n2 n3 n4 n5 n1 n)
          n4 (a2 n2 n3 n4 n5 n1 n) (D n2 n3 n4 n5 n1 n)
        : sub n2 (N n2 n3 n4 n5)}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        N n2 n3 n4 n5 : ty}***
  H9:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H10:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        v n2 n3 n4 n5 n1 n : var n2}***
  H12:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        a2 n2 n3 n4 n5 n1 n :
        bound_var n2 (U2 n2 n3 n4 n5) n4 (v n2 n3 n4 n5 n1 n)}***
  H13:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        D n2 n3 n4 n5 n1 n : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}***
  H14:
      {L, n6:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n7:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n6 (DV n2 n3 n4 n5) |- 
        D4 n5 n4 n3 n2 n1 n n6 n7 : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.2>> prune H14.
  
  Subgoal trans_and_narrow'.3.2:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, U2:
          (o) -> (o) -> (o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> o, P:
          (o) -> (o) -> (o) -> (o) -> o, N:(o) -> (o) -> (o) -> (o) -> o, X:
          (o) -> (o) -> (o) -> (o) -> o, Q:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U2 n2 n3 n4 n5),
              n5:bound_var n2 (U2 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-trans-tvar (U2 n2 n3 n4 n5) (N n2 n3 n4 n5) n2 (v n2 n3 n4 n5 n1 n)
          n4 (a2 n2 n3 n4 n5 n1 n) (D n2 n3 n4 n5 n1 n)
        : sub n2 (N n2 n3 n4 n5)}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        N n2 n3 n4 n5 : ty}***
  H9:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H10:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        v n2 n3 n4 n5 n1 n : var n2}***
  H12:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        a2 n2 n3 n4 n5 n1 n :
        bound_var n2 (U2 n2 n3 n4 n5) n4 (v n2 n3 n4 n5 n1 n)}***
  H13:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        D n2 n3 n4 n5 n1 n : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}***
  H14:
      {L, n6:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n7:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n6 (DV n2 n3 n4 n5) |- 
        D4 n5 n4 n3 n2 n6 n7 : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.2>> apply sub__ty to H14 with (L = L,n1:bound X n2 n3 n4 n5 P n2 n3 n4 n5,
      n:bound_var X n2 n3 n4 n5 P n2 n3 n4 n5 n1 DV n2 n3 n4 n5).
  
  Subgoal trans_and_narrow'.3.2:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, U2:
          (o) -> (o) -> (o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> o, P:
          (o) -> (o) -> (o) -> (o) -> o, N:(o) -> (o) -> (o) -> (o) -> o, X:
          (o) -> (o) -> (o) -> (o) -> o, Q:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U2 n2 n3 n4 n5),
              n5:bound_var n2 (U2 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-trans-tvar (U2 n2 n3 n4 n5) (N n2 n3 n4 n5) n2 (v n2 n3 n4 n5 n1 n)
          n4 (a2 n2 n3 n4 n5 n1 n) (D n2 n3 n4 n5 n1 n)
        : sub n2 (N n2 n3 n4 n5)}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        N n2 n3 n4 n5 : ty}***
  H9:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H10:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        v n2 n3 n4 n5 n1 n : var n2}***
  H12:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        a2 n2 n3 n4 n5 n1 n :
        bound_var n2 (U2 n2 n3 n4 n5) n4 (v n2 n3 n4 n5 n1 n)}***
  H13:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        D n2 n3 n4 n5 n1 n : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}***
  H14:
      {L, n6:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n7:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n6 (DV n2 n3 n4 n5) |- 
        D4 n5 n4 n3 n2 n6 n7 : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}
  H15:
      {L, n1:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n1 (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty} /\
          {L, n1:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n:
            bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n1 (DV n2 n3 n4 n5) |- 
            N n2 n3 n4 n5 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.2>> cases H15.
  
  Subgoal trans_and_narrow'.3.2:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, U2:
          (o) -> (o) -> (o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> o, P:
          (o) -> (o) -> (o) -> (o) -> o, N:(o) -> (o) -> (o) -> (o) -> o, X:
          (o) -> (o) -> (o) -> (o) -> o, Q:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U2 n2 n3 n4 n5),
              n5:bound_var n2 (U2 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-trans-tvar (U2 n2 n3 n4 n5) (N n2 n3 n4 n5) n2 (v n2 n3 n4 n5 n1 n)
          n4 (a2 n2 n3 n4 n5 n1 n) (D n2 n3 n4 n5 n1 n)
        : sub n2 (N n2 n3 n4 n5)}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        N n2 n3 n4 n5 : ty}***
  H9:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H10:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        v n2 n3 n4 n5 n1 n : var n2}***
  H12:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        a2 n2 n3 n4 n5 n1 n :
        bound_var n2 (U2 n2 n3 n4 n5) n4 (v n2 n3 n4 n5 n1 n)}***
  H13:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        D n2 n3 n4 n5 n1 n : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}***
  H14:
      {L, n6:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n7:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n6 (DV n2 n3 n4 n5) |- 
        D4 n5 n4 n3 n2 n6 n7 : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}
  H16:
      {L, n1:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n1 (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}
  H17:
      {L, n1:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n1 (DV n2 n3 n4 n5) |- 
        N n2 n3 n4 n5 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.2>> exists [x]
           [y]
             sa-trans-tvar U2 n2 n3 n4 n5 N n2 n3 n4 n5 n2 n3 n4 n5
               D4 n5 n4 n3 n2 x y.
  
  Subgoal trans_and_narrow'.3.2:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, U2:
          (o) -> (o) -> (o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> o, P:
          (o) -> (o) -> (o) -> (o) -> o, N:(o) -> (o) -> (o) -> (o) -> o, X:
          (o) -> (o) -> (o) -> (o) -> o, Q:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U2 n2 n3 n4 n5),
              n5:bound_var n2 (U2 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-trans-tvar (U2 n2 n3 n4 n5) (N n2 n3 n4 n5) n2 (v n2 n3 n4 n5 n1 n)
          n4 (a2 n2 n3 n4 n5 n1 n) (D n2 n3 n4 n5 n1 n)
        : sub n2 (N n2 n3 n4 n5)}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        N n2 n3 n4 n5 : ty}***
  H9:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H10:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        v n2 n3 n4 n5 n1 n : var n2}***
  H12:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        a2 n2 n3 n4 n5 n1 n :
        bound_var n2 (U2 n2 n3 n4 n5) n4 (v n2 n3 n4 n5 n1 n)}***
  H13:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        D n2 n3 n4 n5 n1 n : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}***
  H14:
      {L, n6:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n7:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n6 (DV n2 n3 n4 n5) |- 
        D4 n5 n4 n3 n2 n6 n7 : sub (U2 n2 n3 n4 n5) (N n2 n3 n4 n5)}
  H16:
      {L, n1:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n1 (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}
  H17:
      {L, n1:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n1 (DV n2 n3 n4 n5) |- 
        N n2 n3 n4 n5 : ty}
  
  ==================================
  {L |- 
    [x
      ][y
         ]sa-trans-tvar (U2 n2 n3 n4 n5) (N n2 n3 n4 n5) n2 n3 n4 n5
            (D4 n5 n4 n3 n2 x y)
    :
    {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
      }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
         }sub n2 (N n2 n3 n4 n5)}
  
  Subgoal trans_and_narrow'.3.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.2>> search.
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: T1:(o) -> (o) -> o, DV1:(o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> o, a2:(o) -> (o) -> (o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, M:
          (o) -> (o) -> o, X:(o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:bound (M n2 n3) (T1 n2 n3), n3:
              bound_var (M n2 n3) (T1 n2 n3) n2 (DV1 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T1 n2 n3) (N n2 n3) (M n2 n3) (v n2 n3 n1 n) n2
          (a2 n2 n3 n1 n) (D n2 n3 n1 n)
        : sub (M n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T1 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- v n2 n3 n1 n :
        var (M n2 n3)}***
  H12:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- a2 n2 n3 n1 n :
        bound_var (M n2 n3) (T1 n2 n3) n2 (v n2 n3 n1 n)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T1 n2 n3) (N n2 n3)}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> cases H12.
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: M1:(o) -> (o) -> o, T2:(o) -> (o) -> o, DV2:(o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, X:
          (o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:bound (M1 n2 n3) (T2 n2 n3), n3:
              bound_var (M1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
          (D n2 n3 n1 n)
        : sub (M1 n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M1 n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T2 n2 n3) (N n2 n3)}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M1 n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> apply IH1 to H3 H4 H5 H13 with X = X n2 n3, M = T2 n2 n3, N = N n2 n3, P =
      P n2 n3, D1 = D1 n2 n3, D2 = [x][y]D n2 n3 y x, DV = DV n2 n3.
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, M1:(o) -> (o) -> o, T2:
          (o) -> (o) -> o, DV2:(o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, X:
          (o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n1, n}:c[(n2:bound (M1 n2 n3) (T2 n2 n3), n3:
              bound_var (M1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
          (D n2 n3 n1 n)
        : sub (M1 n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M1 n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T2 n2 n3) (N n2 n3)}***
  H14:
      {L, n4:bound (X n2 n3) (P n2 n3), n5:
        bound_var (X n2 n3) (P n2 n3) n4 (DV n2 n3) |- D4 n3 n2 n1 n n4 n5 :
        sub (T2 n2 n3) (N n2 n3)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M1 n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> prune H14.
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> o, M1:(o) -> (o) -> o, T2:
          (o) -> (o) -> o, DV2:(o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, X:
          (o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n1, n}:c[(n2:bound (M1 n2 n3) (T2 n2 n3), n3:
              bound_var (M1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
          (D n2 n3 n1 n)
        : sub (M1 n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M1 n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T2 n2 n3) (N n2 n3)}***
  H14:
      {L, n4:bound (X n2 n3) (P n2 n3), n5:
        bound_var (X n2 n3) (P n2 n3) n4 (DV n2 n3) |- D4 n3 n2 n4 n5 :
        sub (T2 n2 n3) (N n2 n3)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M1 n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> apply sub__ty to H14 with (L = L,n1:bound X n2 n3 P n2 n3,
      n:bound_var X n2 n3 P n2 n3 n1 DV n2 n3).
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> o, M1:(o) -> (o) -> o, T2:
          (o) -> (o) -> o, DV2:(o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, X:
          (o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n1, n}:c[(n2:bound (M1 n2 n3) (T2 n2 n3), n3:
              bound_var (M1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
          (D n2 n3 n1 n)
        : sub (M1 n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M1 n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T2 n2 n3) (N n2 n3)}***
  H14:
      {L, n4:bound (X n2 n3) (P n2 n3), n5:
        bound_var (X n2 n3) (P n2 n3) n4 (DV n2 n3) |- D4 n3 n2 n4 n5 :
        sub (T2 n2 n3) (N n2 n3)}
  H15:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- T2 n2 n3 : ty} /\
          {L, n1:bound (X n2 n3) (P n2 n3), n:
            bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- N n2 n3 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M1 n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> cases H15.
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> o, M1:(o) -> (o) -> o, T2:
          (o) -> (o) -> o, DV2:(o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, X:
          (o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n1, n}:c[(n2:bound (M1 n2 n3) (T2 n2 n3), n3:
              bound_var (M1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
          (D n2 n3 n1 n)
        : sub (M1 n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M1 n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T2 n2 n3) (N n2 n3)}***
  H14:
      {L, n4:bound (X n2 n3) (P n2 n3), n5:
        bound_var (X n2 n3) (P n2 n3) n4 (DV n2 n3) |- D4 n3 n2 n4 n5 :
        sub (T2 n2 n3) (N n2 n3)}
  H16:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- T2 n2 n3 : ty}
  H17:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- N n2 n3 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M1 n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> apply narrow_ty to H3 H4 H5 H9.
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> o, M1:(o) -> (o) -> o, T2:
          (o) -> (o) -> o, DV2:(o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, X:
          (o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n9:o, n8:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n5, n4, n1, n}:c[(n2:bound (M1 n2 n3) (T2 n2 n3), n3:
              bound_var (M1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
          (D n2 n3 n1 n)
        : sub (M1 n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M1 n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T2 n2 n3) (N n2 n3)}***
  H14:
      {L, n4:bound (X n2 n3) (P n2 n3), n5:
        bound_var (X n2 n3) (P n2 n3) n4 (DV n2 n3) |- D4 n3 n2 n4 n5 :
        sub (T2 n2 n3) (N n2 n3)}
  H16:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- T2 n2 n3 : ty}
  H17:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- N n2 n3 : ty}
  H18:
      {L, n8:bound (X n2 n3) (P n2 n3), n9:
        bound_var (X n2 n3) (P n2 n3) n8 (DV n2 n3) |- M1 n2 n3 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M1 n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> apply narrow_var to H3 H4 H5 H10.
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> o, M1:(o) -> (o) -> o, T2:
          (o) -> (o) -> o, DV2:(o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, X:
          (o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n11:o, n10:o, n9:o, n8:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n5, n4, n1, n}:c[(n2:
              bound (M1 n2 n3) (T2 n2 n3), n3:
              bound_var (M1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
          (D n2 n3 n1 n)
        : sub (M1 n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M1 n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T2 n2 n3) (N n2 n3)}***
  H14:
      {L, n4:bound (X n2 n3) (P n2 n3), n5:
        bound_var (X n2 n3) (P n2 n3) n4 (DV n2 n3) |- D4 n3 n2 n4 n5 :
        sub (T2 n2 n3) (N n2 n3)}
  H16:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- T2 n2 n3 : ty}
  H17:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- N n2 n3 : ty}
  H18:
      {L, n8:bound (X n2 n3) (P n2 n3), n9:
        bound_var (X n2 n3) (P n2 n3) n8 (DV n2 n3) |- M1 n2 n3 : ty}
  H19:
      {L, n10:bound (X n2 n3) (P n2 n3), n11:
        bound_var (X n2 n3) (P n2 n3) n10 (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M1 n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> exists [x]
           [y]
             sa-trans-tvar T2 n2 n3 N n2 n3 M1 n2 n3 DV2 n2 n3 n2 n3
               D4 n3 n2 x y.
  
  Subgoal trans_and_narrow'.3.3:
  
  Vars: D4:(o) -> (o) -> (o) -> (o) -> o, M1:(o) -> (o) -> o, T2:
          (o) -> (o) -> o, DV2:(o) -> (o) -> o, D:
          (o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> o, D1:
          (o) -> (o) -> o, P:(o) -> (o) -> o, N:(o) -> (o) -> o, X:
          (o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n11:o, n10:o, n9:o, n8:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n5, n4, n1, n}:c[(n2:
              bound (M1 n2 n3) (T2 n2 n3), n3:
              bound_var (M1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
          (D n2 n3 n1 n)
        : sub (M1 n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- M1 n2 n3 : ty}***
  H10:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}***
  H13:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- D n2 n3 n1 n :
        sub (T2 n2 n3) (N n2 n3)}***
  H14:
      {L, n4:bound (X n2 n3) (P n2 n3), n5:
        bound_var (X n2 n3) (P n2 n3) n4 (DV n2 n3) |- D4 n3 n2 n4 n5 :
        sub (T2 n2 n3) (N n2 n3)}
  H16:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- T2 n2 n3 : ty}
  H17:
      {L, n1:bound (X n2 n3) (P n2 n3), n:
        bound_var (X n2 n3) (P n2 n3) n1 (DV n2 n3) |- N n2 n3 : ty}
  H18:
      {L, n8:bound (X n2 n3) (P n2 n3), n9:
        bound_var (X n2 n3) (P n2 n3) n8 (DV n2 n3) |- M1 n2 n3 : ty}
  H19:
      {L, n10:bound (X n2 n3) (P n2 n3), n11:
        bound_var (X n2 n3) (P n2 n3) n10 (DV n2 n3) |- DV2 n2 n3 :
        var (M1 n2 n3)}
  
  ==================================
  {L |- 
    [x
      ][y
         ]sa-trans-tvar (T2 n2 n3) (N n2 n3) (M1 n2 n3) (DV2 n2 n3) n2 n3
            (D4 n3 n2 x y)
    :
    {x:bound (X n2 n3) (P n2 n3)
      }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (M1 n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.4 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.3.3>> search.
  
  Subgoal trans_and_narrow'.4:
  
  Vars: U:(o) -> (o) -> o, v:(o) -> (o) -> o, a1:(o) -> (o) -> o, a2:
          (o) -> (o) -> o, DV:o, D1:o, P:o, N:o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound X Q, n1:bound_var X Q n DV |- 
        sa-refl-tvar (U n1 n) N (v n1 n) (a1 n1 n) (a2 n1 n) : sub N N}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- U n1 n : ty}***
  H8:{L, n:bound X Q, n1:bound_var X Q n DV |- N : ty}***
  H9:{L, n:bound X Q, n1:bound_var X Q n DV |- v n1 n : var N}***
  H10:{L, n:bound X Q, n1:bound_var X Q n DV |- a1 n1 n : bound N (U n1 n)}***
  H11:
      {L, n:bound X Q, n1:bound_var X Q n DV |- a2 n1 n :
        bound_var N (U n1 n) (a1 n1 n) (v n1 n)}***
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub N N}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4>> cases H10.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: v:(o) -> (o) -> o, a2:(o) -> (o) -> o, DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- 
        sa-refl-tvar Q N (v n1 n) n (a2 n1 n) : sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- v n1 n : var N}***
  H11:
      {L, n:bound N Q, n1:bound_var N Q n DV |- a2 n1 n :
        bound_var N Q n (v n1 n)}***
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> cases H11.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> apply narrow_ty to H3 H4 H5 H8.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> apply narrow_var to H3 H4 H5 H9.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> assert {L,n:bound N P,n1:bound_var N P n DV |- P : ty}.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  
  ==================================
  {L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  Subgoal trans_and_narrow'.4.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> apply sub__ty to H5.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  H14:{L |- P : ty} /\ {L |- Q : ty}
  
  ==================================
  {L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  Subgoal trans_and_narrow'.4.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> cases H14.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  H15:{L |- P : ty}
  H16:{L |- Q : ty}
  
  ==================================
  {L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  Subgoal trans_and_narrow'.4.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> strengthen H12.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  H15:{L |- P : ty}
  H16:{L |- Q : ty}
  H17:{L, n2:bound N P |- N : ty}
  
  ==================================
  {L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  Subgoal trans_and_narrow'.4.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> strengthen H13.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  H15:{L |- P : ty}
  H16:{L |- Q : ty}
  H17:{L, n2:bound N P |- N : ty}
  H18:{L, n4:bound N P |- DV : var N}
  
  ==================================
  {L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  Subgoal trans_and_narrow'.4.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> weaken H15 with bound N P.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  H15:{L |- P : ty}
  H16:{L |- Q : ty}
  H17:{L, n2:bound N P |- N : ty}
  H18:{L, n4:bound N P |- DV : var N}
  H19:{L, n6:bound N P |- P : ty}
  
  ==================================
  {L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  Subgoal trans_and_narrow'.4.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> weaken H19 with bound_var N P n6 DV.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n7:o, n6:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  H15:{L |- P : ty}
  H16:{L |- Q : ty}
  H17:{L, n2:bound N P |- N : ty}
  H18:{L, n4:bound N P |- DV : var N}
  H19:{L, n6:bound N P |- P : ty}
  H20:{L, n6:bound N P, n7:bound_var N P n6 DV |- P : ty}
  
  ==================================
  {L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  Subgoal trans_and_narrow'.4.1 is:
   exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> search.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  H14:{L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> exists [x][y]sa-refl-tvar P N DV x y.
  
  Subgoal trans_and_narrow'.4.1:
  
  Vars: DV:o, D1:o, P:o, N:o, Q:o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n5, n4, n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- N : ty}
  H4:{L |- DV : var N}
  H5:{L |- D1 : sub P Q}
  H6:
      {L, n:bound N Q, n1:bound_var N Q n DV |- sa-refl-tvar Q N DV n n1 :
        sub N N}@@@
  H7:{L, n:bound N Q, n1:bound_var N Q n DV |- Q : ty}***
  H8:{L, n:bound N Q, n1:bound_var N Q n DV |- N : ty}***
  H9:{L, n:bound N Q, n1:bound_var N Q n DV |- DV : var N}***
  H12:{L, n2:bound N P, n3:bound_var N P n2 DV |- N : ty}
  H13:{L, n4:bound N P, n5:bound_var N P n4 DV |- DV : var N}
  H14:{L, n:bound N P, n1:bound_var N P n DV |- P : ty}
  
  ==================================
  {L |- [x][y]sa-refl-tvar P N DV x y :
    {x:bound N P}{y:bound_var N P x DV}sub N N}
  
  Subgoal trans_and_narrow'.4.2 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
         }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
            }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.1>> search.
  
  Subgoal trans_and_narrow'.4.2:
  
  Vars: U2:(o) -> (o) -> (o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> o, P:
          (o) -> (o) -> (o) -> (o) -> o, M:(o) -> (o) -> (o) -> (o) -> o, X:
          (o) -> (o) -> (o) -> (o) -> o, Q:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U2 n2 n3 n4 n5), n5:
              bound_var n2 (U2 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-refl-tvar (U2 n2 n3 n4 n5) n2 (v n2 n3 n4 n5 n1 n) n4
          (a2 n2 n3 n4 n5 n1 n)
        : sub n2 n2}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H9:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        v n2 n3 n4 n5 n1 n : var n2}***
  H11:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        a2 n2 n3 n4 n5 n1 n :
        bound_var n2 (U2 n2 n3 n4 n5) n4 (v n2 n3 n4 n5 n1 n)}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.2>> cases H9.
  
  Subgoal trans_and_narrow'.4.2:
  
  Vars: U2:(o) -> (o) -> (o) -> (o) -> o, a2:
          (o) -> (o) -> (o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> (o) -> (o) -> o, D1:(o) -> (o) -> (o) -> (o) -> o, P:
          (o) -> (o) -> (o) -> (o) -> o, M:(o) -> (o) -> (o) -> (o) -> o, X:
          (o) -> (o) -> (o) -> (o) -> o, Q:(o) -> (o) -> (o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U2 n2 n3 n4 n5), n5:
              bound_var n2 (U2 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-refl-tvar (U2 n2 n3 n4 n5) n2 n3 n4 (a2 n2 n3 n4 n5 n1 n) :
        sub n2 n2}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U2 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H11:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        a2 n2 n3 n4 n5 n1 n : bound_var n2 (U2 n2 n3 n4 n5) n4 n3}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.2>> cases H11.
  
  Subgoal trans_and_narrow'.4.2:
  
  Vars: U3:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> (o) -> (o) -> (o) -> o, P:(o) -> (o) -> (o) -> (o) -> o, M:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o, Q:
          (o) -> (o) -> (o) -> (o) -> o
  Nominals: n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:ty, n3:var n2, n4:bound n2 (U3 n2 n3 n4 n5), n5:
              bound_var n2 (U3 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-refl-tvar (U3 n2 n3 n4 n5) n2 n3 n4 n5 : sub n2 n2}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U3 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.2>> apply narrow_ty to H3 H4 H5 H7.
  
  Subgoal trans_and_narrow'.4.2:
  
  Vars: U3:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> (o) -> (o) -> (o) -> o, P:(o) -> (o) -> (o) -> (o) -> o, M:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o, Q:
          (o) -> (o) -> (o) -> (o) -> o
  Nominals: n11:o, n10:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n1, n}:c[(n2:ty, n3:var n2, n4:
              bound n2 (U3 n2 n3 n4 n5), n5:
              bound_var n2 (U3 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-refl-tvar (U3 n2 n3 n4 n5) n2 n3 n4 n5 : sub n2 n2}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U3 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H12:
      {L, n10:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n11:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n10 (DV n2 n3 n4 n5) |- 
        U3 n2 n3 n4 n5 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
        }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
           }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.2>> exists [x][y]sa-refl-tvar U3 n2 n3 n4 n5 n2 n3 n4 n5.
  
  Subgoal trans_and_narrow'.4.2:
  
  Vars: U3:(o) -> (o) -> (o) -> (o) -> o, DV:(o) -> (o) -> (o) -> (o) -> o, D1:
          (o) -> (o) -> (o) -> (o) -> o, P:(o) -> (o) -> (o) -> (o) -> o, M:
          (o) -> (o) -> (o) -> (o) -> o, X:(o) -> (o) -> (o) -> (o) -> o, Q:
          (o) -> (o) -> (o) -> (o) -> o
  Nominals: n11:o, n10:o, n5:o, n4:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n1, n}:c[(n2:ty, n3:var n2, n4:
              bound n2 (U3 n2 n3 n4 n5), n5:
              bound_var n2 (U3 n2 n3 n4 n5) n4 n3)], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 n4 n5 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3 n4 n5)} =>
              {L |- D2 : sub (Q n2 n3 n4 n5) T} =>
                  exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3 n4 n5)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3 n4 n5)
                          }{y:bound_var X (Q n2 n3 n4 n5) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 n4 n5 : ty}
  H4:{L |- DV n2 n3 n4 n5 : var (X n2 n3 n4 n5)}
  H5:{L |- D1 n2 n3 n4 n5 : sub (P n2 n3 n4 n5) (Q n2 n3 n4 n5)}
  H6:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        sa-refl-tvar (U3 n2 n3 n4 n5) n2 n3 n4 n5 : sub n2 n2}@@@
  H7:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- 
        U3 n2 n3 n4 n5 : ty}***
  H8:
      {L, n:bound (X n2 n3 n4 n5) (Q n2 n3 n4 n5), n1:
        bound_var (X n2 n3 n4 n5) (Q n2 n3 n4 n5) n (DV n2 n3 n4 n5) |- n2 :
        ty}***
  H12:
      {L, n10:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5), n11:
        bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) n10 (DV n2 n3 n4 n5) |- 
        U3 n2 n3 n4 n5 : ty}
  
  ==================================
  {L |- [x][y]sa-refl-tvar (U3 n2 n3 n4 n5) n2 n3 n4 n5 :
    {x:bound (X n2 n3 n4 n5) (P n2 n3 n4 n5)
      }{y:bound_var (X n2 n3 n4 n5) (P n2 n3 n4 n5) x (DV n2 n3 n4 n5)
         }sub n2 n2}
  
  Subgoal trans_and_narrow'.4.3 is:
   exists D4,
     {L |- [x][y]D4 x y :
       {x:bound (X n2 n3) (P n2 n3)
         }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.2>> search.
  
  Subgoal trans_and_narrow'.4.3:
  
  Vars: T1:(o) -> (o) -> o, DV1:(o) -> (o) -> o, v:
          (o) -> (o) -> (o) -> (o) -> o, a2:(o) -> (o) -> (o) -> (o) -> o, DV:
          (o) -> (o) -> o, D1:(o) -> (o) -> o, P:(o) -> (o) -> o, N:
          (o) -> (o) -> o, M:(o) -> (o) -> o, X:(o) -> (o) -> o, Q:
          (o) -> (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:bound (N n2 n3) (T1 n2 n3), n3:
              bound_var (N n2 n3) (T1 n2 n3) n2 (DV1 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-refl-tvar (T1 n2 n3) (N n2 n3) (v n2 n3 n1 n) n2 (a2 n2 n3 n1 n) :
        sub (N n2 n3) (N n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T1 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- v n2 n3 n1 n :
        var (N n2 n3)}***
  H11:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- a2 n2 n3 n1 n :
        bound_var (N n2 n3) (T1 n2 n3) n2 (v n2 n3 n1 n)}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N n2 n3) (N n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.3>> cases H11.
  
  Subgoal trans_and_narrow'.4.3:
  
  Vars: N1:(o) -> (o) -> o, T2:(o) -> (o) -> o, DV2:(o) -> (o) -> o, DV:
          (o) -> (o) -> o, D1:(o) -> (o) -> o, P:(o) -> (o) -> o, M:
          (o) -> (o) -> o, X:(o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n1, n}:c[(n2:bound (N1 n2 n3) (T2 n2 n3), n3:
              bound_var (N1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-refl-tvar (T2 n2 n3) (N1 n2 n3) (DV2 n2 n3) n2 n3 :
        sub (N1 n2 n3) (N1 n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N1 n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (N1 n2 n3)}***
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)
           }sub (N1 n2 n3) (N1 n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.3>> apply narrow_ty to H3 H4 H5 H7.
  
  Subgoal trans_and_narrow'.4.3:
  
  Vars: N1:(o) -> (o) -> o, T2:(o) -> (o) -> o, DV2:(o) -> (o) -> o, DV:
          (o) -> (o) -> o, D1:(o) -> (o) -> o, P:(o) -> (o) -> o, M:
          (o) -> (o) -> o, X:(o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n7:o, n6:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n7, n6, n1, n}:c[(n2:bound (N1 n2 n3) (T2 n2 n3), n3:
              bound_var (N1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-refl-tvar (T2 n2 n3) (N1 n2 n3) (DV2 n2 n3) n2 n3 :
        sub (N1 n2 n3) (N1 n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N1 n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (N1 n2 n3)}***
  H12:
      {L, n6:bound (X n2 n3) (P n2 n3), n7:
        bound_var (X n2 n3) (P n2 n3) n6 (DV n2 n3) |- T2 n2 n3 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)
           }sub (N1 n2 n3) (N1 n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.3>> apply narrow_ty to H3 H4 H5 H8.
  
  Subgoal trans_and_narrow'.4.3:
  
  Vars: N1:(o) -> (o) -> o, T2:(o) -> (o) -> o, DV2:(o) -> (o) -> o, DV:
          (o) -> (o) -> o, D1:(o) -> (o) -> o, P:(o) -> (o) -> o, M:
          (o) -> (o) -> o, X:(o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n9:o, n8:o, n7:o, n6:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n9, n8, n7, n6, n1, n}:c[(n2:bound (N1 n2 n3) (T2 n2 n3), n3:
              bound_var (N1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-refl-tvar (T2 n2 n3) (N1 n2 n3) (DV2 n2 n3) n2 n3 :
        sub (N1 n2 n3) (N1 n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N1 n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (N1 n2 n3)}***
  H12:
      {L, n6:bound (X n2 n3) (P n2 n3), n7:
        bound_var (X n2 n3) (P n2 n3) n6 (DV n2 n3) |- T2 n2 n3 : ty}
  H13:
      {L, n8:bound (X n2 n3) (P n2 n3), n9:
        bound_var (X n2 n3) (P n2 n3) n8 (DV n2 n3) |- N1 n2 n3 : ty}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)
           }sub (N1 n2 n3) (N1 n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.3>> apply narrow_var to H3 H4 H5 H9.
  
  Subgoal trans_and_narrow'.4.3:
  
  Vars: N1:(o) -> (o) -> o, T2:(o) -> (o) -> o, DV2:(o) -> (o) -> o, DV:
          (o) -> (o) -> o, D1:(o) -> (o) -> o, P:(o) -> (o) -> o, M:
          (o) -> (o) -> o, X:(o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n1, n}:c[(n2:
              bound (N1 n2 n3) (T2 n2 n3), n3:
              bound_var (N1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-refl-tvar (T2 n2 n3) (N1 n2 n3) (DV2 n2 n3) n2 n3 :
        sub (N1 n2 n3) (N1 n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N1 n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (N1 n2 n3)}***
  H12:
      {L, n6:bound (X n2 n3) (P n2 n3), n7:
        bound_var (X n2 n3) (P n2 n3) n6 (DV n2 n3) |- T2 n2 n3 : ty}
  H13:
      {L, n8:bound (X n2 n3) (P n2 n3), n9:
        bound_var (X n2 n3) (P n2 n3) n8 (DV n2 n3) |- N1 n2 n3 : ty}
  H14:
      {L, n10:bound (X n2 n3) (P n2 n3), n11:
        bound_var (X n2 n3) (P n2 n3) n10 (DV n2 n3) |- DV2 n2 n3 :
        var (N1 n2 n3)}
  
  ==================================
  exists D4,
    {L |- [x][y]D4 x y :
      {x:bound (X n2 n3) (P n2 n3)
        }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)
           }sub (N1 n2 n3) (N1 n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.3>> exists [x][y]sa-refl-tvar T2 n2 n3 N1 n2 n3 DV2 n2 n3 n2 n3.
  
  Subgoal trans_and_narrow'.4.3:
  
  Vars: N1:(o) -> (o) -> o, T2:(o) -> (o) -> o, DV2:(o) -> (o) -> o, DV:
          (o) -> (o) -> o, D1:(o) -> (o) -> o, P:(o) -> (o) -> o, M:
          (o) -> (o) -> o, X:(o) -> (o) -> o, Q:(o) -> (o) -> o
  Nominals: n11:o, n10:o, n9:o, n8:o, n7:o, n6:o, n3:o, n2:o, n1:o, n:o
  Contexts: L{n11, n10, n9, n8, n7, n6, n1, n}:c[(n2:
              bound (N1 n2 n3) (T2 n2 n3), n3:
              bound_var (N1 n2 n3) (T2 n2 n3) n2 (DV2 n2 n3))], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q n2 n3 : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S (Q n2 n3)} =>
              {L |- D2 : sub (Q n2 n3) T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P (Q n2 n3)} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X (Q n2 n3)
                          }{y:bound_var X (Q n2 n3) x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X n2 n3 : ty}
  H4:{L |- DV n2 n3 : var (X n2 n3)}
  H5:{L |- D1 n2 n3 : sub (P n2 n3) (Q n2 n3)}
  H6:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- 
        sa-refl-tvar (T2 n2 n3) (N1 n2 n3) (DV2 n2 n3) n2 n3 :
        sub (N1 n2 n3) (N1 n2 n3)}@@@
  H7:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- T2 n2 n3 : ty}***
  H8:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- N1 n2 n3 : ty}***
  H9:
      {L, n:bound (X n2 n3) (Q n2 n3), n1:
        bound_var (X n2 n3) (Q n2 n3) n (DV n2 n3) |- DV2 n2 n3 :
        var (N1 n2 n3)}***
  H12:
      {L, n6:bound (X n2 n3) (P n2 n3), n7:
        bound_var (X n2 n3) (P n2 n3) n6 (DV n2 n3) |- T2 n2 n3 : ty}
  H13:
      {L, n8:bound (X n2 n3) (P n2 n3), n9:
        bound_var (X n2 n3) (P n2 n3) n8 (DV n2 n3) |- N1 n2 n3 : ty}
  H14:
      {L, n10:bound (X n2 n3) (P n2 n3), n11:
        bound_var (X n2 n3) (P n2 n3) n10 (DV n2 n3) |- DV2 n2 n3 :
        var (N1 n2 n3)}
  
  ==================================
  {L |- [x][y]sa-refl-tvar (T2 n2 n3) (N1 n2 n3) (DV2 n2 n3) n2 n3 :
    {x:bound (X n2 n3) (P n2 n3)
      }{y:bound_var (X n2 n3) (P n2 n3) x (DV n2 n3)}sub (N1 n2 n3) (N1 n2 n3)}
  
  Subgoal trans_and_narrow'.5 is:
   exists D4,
     {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.4.3>> search.
  
  Subgoal trans_and_narrow'.5:
  
  Vars: DV:o, D1:o, P:o, M:o, X:o, Q:o
  Nominals: n1:o, n:o
  Contexts: L{n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:{L, n:bound X Q, n1:bound_var X Q n DV |- sa-top M : sub M top}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M : ty}***
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.5>> apply narrow_ty to H3 H4 H5 H7.
  
  Subgoal trans_and_narrow'.5:
  
  Vars: DV:o, D1:o, P:o, M:o, X:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:{L, n:bound X Q, n1:bound_var X Q n DV |- sa-top M : sub M top}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M : ty}***
  H8:{L, n2:bound X P, n3:bound_var X P n2 DV |- M : ty}
  
  ==================================
  exists D4, {L |- [x][y]D4 x y : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.5>> exists [x][y]sa-top M.
  
  Subgoal trans_and_narrow'.5:
  
  Vars: DV:o, D1:o, P:o, M:o, X:o, Q:o
  Nominals: n3:o, n2:o, n1:o, n:o
  Contexts: L{n3, n2, n1, n}:c[], G{}:wf[]
  IH:
      forall Q,
        ctx G:wf.
          {G |- Q : ty}* =>
              ctx L:c.
                forall S, forall T, forall D1, forall D2,
                  {L |- D1 : sub S Q} =>
                      {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
                  /\
                  ctx L:c.
                    forall X, forall M, forall N, forall P, forall D1,
                      forall D2, forall DV,
                      {L |- X : ty} =>
                          {L |- DV : var X} =>
                              {L |- D1 : sub P Q} =>
                                  {L |- [x][y]D2 x y :
                                    {x:bound X Q}{y:bound_var X Q x DV}sub M N}
                                      =>
                                      exists D4,
                                        {L |- [x][y]D4 x y :
                                          {x:bound X P
                                            }{y:bound_var X P x DV}sub M N}
  H1:{G |- Q : ty}@
  H2:
      ctx L:c.
        forall S, forall T, forall D1, forall D2,
          {L |- D1 : sub S Q} =>
              {L |- D2 : sub Q T} => exists D3, {L |- D3 : sub S T}
  IH1:
      ctx L:c.
        forall X, forall M, forall N, forall P, forall D1, forall D2,
          forall DV,
          {L |- X : ty} =>
              {L |- DV : var X} =>
                  {L |- D1 : sub P Q} =>
                      {L |- [x][y]D2 x y :
                        {x:bound X Q}{y:bound_var X Q x DV}sub M N}*** =>
                          exists D4,
                            {L |- [x][y]D4 x y :
                              {x:bound X P}{y:bound_var X P x DV}sub M N}
  H3:{L |- X : ty}
  H4:{L |- DV : var X}
  H5:{L |- D1 : sub P Q}
  H6:{L, n:bound X Q, n1:bound_var X Q n DV |- sa-top M : sub M top}@@@
  H7:{L, n:bound X Q, n1:bound_var X Q n DV |- M : ty}***
  H8:{L, n2:bound X P, n3:bound_var X P n2 DV |- M : ty}
  
  ==================================
  {L |- [x][y]sa-top M : {x:bound X P}{y:bound_var X P x DV}sub M top}
  
  trans_and_narrow'.5>> search.
  Proof Completed!
  
  >> Goodbye!
