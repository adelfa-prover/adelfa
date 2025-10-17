  $ adelfa -i assertion.ath
  Welcome!
  >> Specification "stlc.lf".
  
  >> Theorem new-nominals: forall  X, {X : tm} => false.
  
  Subgoal new-nominals:
  
  
  ==================================
  forall X, {X : tm} => False
  
  new-nominals>> intros.
  
  Subgoal new-nominals:
  
  Vars: X:o
  H1:{X : tm}
  
  ==================================
  False
  
  new-nominals>> assert {n:tm |- X : tm}.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n:o
  H1:{X : tm}
  
  ==================================
  {n:tm |- X : tm}
  
  Subgoal new-nominals is:
   False
  
  new-nominals>> weaken H1 with tm.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n1:o, n:o
  H1:{X : tm}
  H2:{n1:tm |- X : tm}
  
  ==================================
  {n:tm |- X : tm}
  
  Subgoal new-nominals is:
   False
  
  new-nominals>> search.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n:o
  H1:{X : tm}
  H2:{n:tm |- X : tm}
  
  ==================================
  False
  
  new-nominals>> assert {u:{_:tm}tm |- X : tm}.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n1:(o) -> o, n:o
  H1:{X : tm}
  H2:{n:tm |- X : tm}
  
  ==================================
  {n1:{_:tm}tm |- X : tm}
  
  Subgoal new-nominals is:
   False
  
  new-nominals>> weaken H1 with {_:tm}tm.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n2:(o) -> o, n1:(o) -> o, n:o
  H1:{X : tm}
  H2:{n:tm |- X : tm}
  H3:{n2:{_:tm}tm |- X : tm}
  
  ==================================
  {n1:{_:tm}tm |- X : tm}
  
  Subgoal new-nominals is:
   False
  
  new-nominals>> search.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n1:(o) -> o, n:o
  H1:{X : tm}
  H2:{n:tm |- X : tm}
  H3:{n1:{_:tm}tm |- X : tm}
  
  ==================================
  False
  
  new-nominals>> assert {n:tp |- X : tm}.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n1:(o) -> o, n:o
  H1:{X : tm}
  H2:{n:tm |- X : tm}
  H3:{n1:{_:tm}tm |- X : tm}
  
  ==================================
  {n:tp |- X : tm}
  
  Subgoal new-nominals is:
   False
  
  new-nominals>> weaken H1 with tp.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n2:o, n1:(o) -> o, n:o
  H1:{X : tm}
  H2:{n:tm |- X : tm}
  H3:{n1:{_:tm}tm |- X : tm}
  H4:{n2:tp |- X : tm}
  
  ==================================
  {n:tp |- X : tm}
  
  Subgoal new-nominals is:
   False
  
  new-nominals>> search.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n1:(o) -> o, n:o
  H1:{X : tm}
  H2:{n:tm |- X : tm}
  H3:{n1:{_:tm}tm |- X : tm}
  H4:{n:tp |- X : tm}
  
  ==================================
  False
  
  new-nominals>> assert {v:{_:tp}tp,g:{_:tp}tp |- X : tm}.
  
  Subgoal new-nominals:
  
  Vars: X:o
  Nominals: n2:(o) -> o, n3:(o) -> o, n1:(o) -> o, n:o
  H1:{X : tm}
  H2:{n:tm |- X : tm}
  H3:{n1:{_:tm}tm |- X : tm}
  H4:{n:tp |- X : tm}
  
  ==================================
  {n2:{_:tp}tp, n3:{_:tp}tp |- X : tm}
  
  Subgoal new-nominals is:
   False
  
  new-nominals>> abort.
  Proof Aborted.
  
  >> Goodbye!
