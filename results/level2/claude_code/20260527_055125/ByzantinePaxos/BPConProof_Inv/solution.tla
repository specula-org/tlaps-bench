
---------------------------- MODULE BPConProof_Inv ------------------------------

EXTENDS Integers, FiniteSets, TLAPS
-----------------------------------------------------------------------------

AXIOM EmptySetFinite == IsFiniteSet({})

AXIOM SingletonSetFinite == \A e : IsFiniteSet({e})

AXIOM ImageOfFiniteSetFinite == 
         \A S, f : IsFiniteSet(S) => IsFiniteSet({f[x] : x \in S})

AXIOM SubsetOfFiniteSetFinite == 
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

AXIOM UnionOfFiniteSetsFinite == 
        \A S, T : IsFiniteSet(T) /\ IsFiniteSet(S)  => IsFiniteSet(S \cup T)

----------------------------------------------------------------------------

CONSTANT Value

Ballot == Nat

None == CHOOSE v : v \notin Value
-----------------------------------------------------------------------------  

CONSTANTS Acceptor,       
          FakeAcceptor,   
          ByzQuorum,     

          WeakQuorum     

ByzAcceptor == Acceptor \cup FakeAcceptor

ASSUME BallotAssump == (Ballot \cup {-1}) \cap ByzAcceptor = {}

ASSUME BQA == 
          /\ Acceptor \cap FakeAcceptor = {}
          /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
          /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
          /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                                   /\ Q \cap Acceptor # {}

ASSUME BQLA == 
          /\ \E Q \in ByzQuorum : Q \subseteq Acceptor 
          /\ \E Q \in WeakQuorum : Q \subseteq Acceptor 
-----------------------------------------------------------------------------

1aMessage == [type : {"1a"},  bal : Ballot]

1bMessage == 

  [type : {"1b"}, bal : Ballot, 
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

1cMessage == 

  [type : {"1c"}, bal : Ballot, val : Value] 

2avMessage ==

   [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]

BMessage == 
  1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage

-----------------------------------------------------------------------------

VARIABLES maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs

sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}

KnowsSafeAt(ac, b, v) ==
  LET S == {m \in knowsSent[ac] : m.bal = b}
  IN  \/ \E BQ \in ByzQuorum :
           \A a \in BQ : \E m \in S : /\ m.acc = a
                                      /\ m.mbal = -1
      \/ \E c \in 0..(b-1):
           /\ \E BQ \in ByzQuorum :
                \A a \in BQ : \E m \in S : /\ m.acc = a
                                           /\ m.mbal =< c
                                           /\ (m.mbal = c) => (m.mval = v)
           /\ \E WQ \in WeakQuorum :
                \A a \in WQ :
                  \E m \in S : /\ m.acc = a
                               /\ \E r \in m.m2av : /\ r.bal >= c
                                                    /\ r.val = v

vars == << maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs >>

Init == 
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ 2avSent = [a \in Acceptor |-> {}]
        /\ knowsSent = [a \in Acceptor |-> {}]
        /\ bmsgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ bmsgs' = (bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                                                 m2av |-> 2avSent[self],
                                                 mbal |-> maxVBal[self], mval |-> maxVVal[self]]})
                       /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>
                    \/ /\ /\ maxBal[self] =< b
                          /\ \A r \in 2avSent[self] : r.bal < b
                       /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
                            /\ bmsgs' = (bmsgs \cup
                                          {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]})
                            /\ 2avSent' = [2avSent EXCEPT ![self] = {r \in 2avSent[self] : r.val # m.val}
                                                                      \cup {[val |-> m.val, bal |-> b]}]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>
                    \/ /\ maxBal[self] =< b
                       /\ \E v \in {vv \in Value :
                                      \E Q \in ByzQuorum :
                                         \A aa \in Q :
                                            \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                                          /\ m.acc = aa}:
                            /\ bmsgs' = (bmsgs \cup
                                          {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
                            /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                       /\ UNCHANGED <<2avSent, knowsSent>>
                    \/ /\ \E S \in SUBSET sentMsgs("1b", b):
                            knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
                       /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

leader(self) == /\ \/ /\ bmsgs' = (bmsgs \cup {[type |-> "1a", bal |-> self]})
                   \/ /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                           bmsgs' = (bmsgs \cup S)
                /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

facceptor(self) == /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
                                 mm.acc = self}:
                        bmsgs' = (bmsgs \cup {m})
                   /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, 
                                   knowsSent >>

Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))
           \/ (\E self \in FakeAcceptor: facceptor(self))

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

Quorum == {S \cap Acceptor : S \in ByzQuorum}

msgsOfType(t) == {m \in bmsgs : m.type = t }

acceptorMsgsOfType(t) == {m \in msgsOfType(t) : m.acc \in  Acceptor}
 
1bRestrict(m) == [type |-> "1b", acc |-> m.acc, bal |-> m.bal, 
                  mbal |-> m.mbal, mval |-> m.mval]

1bmsgs == { 1bRestrict(m) : m \in acceptorMsgsOfType("1b") }

1cmsgs == {m \in msgsOfType("1c") :
                   \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}

2amsgs == {m \in [type : {"2a"}, bal : Ballot, val : Value] :
             \E Q \in Quorum :
               \A a \in Q :
                 \E m2av \in acceptorMsgsOfType("2av") : 
                    /\ m2av.acc = a
                    /\ m2av.bal = m.bal
                    /\ m2av.val = m.val }

msgs == msgsOfType("1a") \cup 1bmsgs \cup 1cmsgs \cup 2amsgs 
         \cup acceptorMsgsOfType("2b")

AXIOM FiniteSetHasMax == 
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

1bOr2bMsgs == {m \in bmsgs : m.type \in {"1b", "2b"}}

-----------------------------------------------------------------------------

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ 2avSent \in [Acceptor -> SUBSET [val : Value, bal : Ballot]]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ knowsSent \in [Acceptor -> SUBSET 1bMessage]
          /\ bmsgs \subseteq BMessage

bmsgsFinite == IsFiniteSet(1bOr2bMsgs)

1bInv1 == \A m \in bmsgs  :
             /\ m.type = "1b"
             /\ m.acc \in Acceptor
             => \A r \in m.m2av :
                [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

1bInv2 == \A m1, m2 \in bmsgs  :
             /\ m1.type = "1b"
             /\ m2.type = "1b"
             /\ m1.acc \in Acceptor
             /\ m1.acc = m2.acc
             /\ m1.bal = m2.bal
             => m1 = m2

2avInv1 == \A m1, m2 \in bmsgs :
             /\ m1.type = "2av"
             /\ m2.type = "2av"
             /\ m1.acc \in Acceptor
             /\ m1.acc = m2.acc
             /\ m1.bal = m2.bal
             => m1 = m2

2avInv2 == \A m \in bmsgs : 
             /\ m.type = "2av"
             /\ m.acc \in Acceptor
             => \E r \in 2avSent[m.acc] : /\ r.val = m.val 
                                          /\ r.bal >= m.bal

2avInv3 == \A m \in bmsgs : 
             /\ m.type = "2av"
             /\ m.acc \in Acceptor
             => [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs

maxBalInv == \A m \in bmsgs :
               /\ m.type \in {"1b", "2av", "2b"}
               /\ m.acc \in Acceptor
               => m.bal =< maxBal[m.acc]

accInv == \A a \in Acceptor :
            \A r \in 2avSent[a] : 
              /\ r.bal =< maxBal[a]
              /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

knowsSentInv == \A a \in Acceptor : knowsSent[a] \subseteq msgsOfType("1b")

Inv == 
 TypeOK /\ bmsgsFinite /\ 1bInv1 /\ 1bInv2 /\ maxBalInv  /\ 2avInv1 /\ 2avInv2 
   /\ 2avInv3 /\ accInv /\ knowsSentInv
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

LEMMA KnowsSafeAtMono ==
  ASSUME NEW ac \in Acceptor, NEW b, NEW v,
         \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a],
         KnowsSafeAt(ac, b, v)
  PROVE  KnowsSafeAt(ac, b, v)'
PROOF
  <1>1. knowsSent[ac] \subseteq knowsSent'[ac]
    OBVIOUS
  <1> QED
    BY <1>1 DEF KnowsSafeAt

LEMMA MsgsMonotone ==
  ASSUME bmsgs \subseteq bmsgs',
         \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
  PROVE  msgs \subseteq msgs'
PROOF
  <1>1. msgsOfType("1a") \subseteq (msgsOfType("1a"))'
    BY DEF msgsOfType
  <1>2. 1bmsgs \subseteq 1bmsgs'
    BY DEF 1bmsgs, acceptorMsgsOfType, msgsOfType, 1bRestrict
  <1>3. 1cmsgs \subseteq 1cmsgs'
    <2> SUFFICES ASSUME NEW m \in 1cmsgs PROVE m \in 1cmsgs'
      OBVIOUS
    <2>1. m \in msgsOfType("1c")
      BY DEF 1cmsgs
    <2>2. m \in (msgsOfType("1c"))'
      BY <2>1 DEF msgsOfType
    <2>3. \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
      BY DEF 1cmsgs
    <2>4. \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)'
      <3>1. PICK a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
        BY <2>3
      <3>2. KnowsSafeAt(a, m.bal, m.val)'
        BY <3>1, KnowsSafeAtMono
      <3> QED
        BY <3>2
    <2> QED
      BY <2>2, <2>4 DEF 1cmsgs
  <1>4. 2amsgs \subseteq 2amsgs'
    <2> SUFFICES ASSUME NEW m \in 2amsgs PROVE m \in 2amsgs'
      OBVIOUS
    <2>1. m \in [type : {"2a"}, bal : Ballot, val : Value]
      BY DEF 2amsgs
    <2>2. \E Q \in Quorum : \A a \in Q :
            \E m2av \in acceptorMsgsOfType("2av") :
               /\ m2av.acc = a
               /\ m2av.bal = m.bal
               /\ m2av.val = m.val
      BY DEF 2amsgs
    <2>3. acceptorMsgsOfType("2av") \subseteq (acceptorMsgsOfType("2av"))'
      BY DEF acceptorMsgsOfType, msgsOfType
    <2>4. \E Q \in Quorum : \A a \in Q :
            \E m2av \in (acceptorMsgsOfType("2av"))' :
               /\ m2av.acc = a
               /\ m2av.bal = m.bal
               /\ m2av.val = m.val
      BY <2>2, <2>3
    <2> QED
      BY <2>1, <2>4 DEF 2amsgs, Quorum, Ballot
  <1>5. acceptorMsgsOfType("2b") \subseteq (acceptorMsgsOfType("2b"))'
    BY DEF acceptorMsgsOfType, msgsOfType
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF msgs

LEMMA MsgTypeLemma ==
  ASSUME TypeOK, NEW mm \in bmsgs
  PROVE  /\ (mm.type = "1a")  => mm \in 1aMessage
         /\ (mm.type = "1b")  => mm \in 1bMessage
         /\ (mm.type = "1c")  => mm \in 1cMessage
         /\ (mm.type = "2av") => mm \in 2avMessage
         /\ (mm.type = "2b")  => mm \in 2bMessage
PROOF
  BY DEF TypeOK, BMessage, 1aMessage, 1bMessage, 1cMessage, 2avMessage, 2bMessage

LEMMA LemStutter ==
  ASSUME Inv, UNCHANGED vars
  PROVE  Inv'
PROOF
  <1> USE DEF vars, Inv
  <1>0. /\ maxBal' = maxBal
        /\ maxVBal' = maxVBal
        /\ maxVVal' = maxVVal
        /\ 2avSent' = 2avSent
        /\ knowsSent' = knowsSent
        /\ bmsgs' = bmsgs
    OBVIOUS
  <1>m. msgs \subseteq msgs'
    BY <1>0, MsgsMonotone
  <1>1. TypeOK'
    BY <1>0 DEF TypeOK
  <1>2. bmsgsFinite'
    BY <1>0 DEF bmsgsFinite, 1bOr2bMsgs
  <1>3. 1bInv1'
    BY <1>0, <1>m DEF 1bInv1
  <1>4. 1bInv2'
    BY <1>0 DEF 1bInv2
  <1>5. maxBalInv'
    BY <1>0 DEF maxBalInv
  <1>6. 2avInv1'
    BY <1>0 DEF 2avInv1
  <1>7. 2avInv2'
    BY <1>0 DEF 2avInv2
  <1>8. 2avInv3'
    BY <1>0, <1>m DEF 2avInv3
  <1>9. accInv'
    BY <1>0, <1>m DEF accInv
  <1>10. knowsSentInv'
    BY <1>0 DEF knowsSentInv, msgsOfType
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

LL1(self) == /\ bmsgs' = (bmsgs \cup {[type |-> "1a", bal |-> self]})
             /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

LL2(self) == /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                  bmsgs' = (bmsgs \cup S)
             /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

LEMMA LemL1 ==
  ASSUME Inv, NEW self \in Ballot, LL1(self)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv
  <1>0. /\ bmsgs' = bmsgs \cup {[type |-> "1a", bal |-> self]}
        /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVVal' = maxVVal
        /\ 2avSent' = 2avSent /\ knowsSent' = knowsSent
    BY DEF LL1
  <1>nm. [type |-> "1a", bal |-> self] \in 1aMessage
    BY DEF 1aMessage
  <1>sub. bmsgs \subseteq bmsgs'
    BY <1>0
  <1>sub2. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    BY <1>0
  <1>m. msgs \subseteq msgs'
    BY <1>sub, <1>sub2, MsgsMonotone
  <1>1. TypeOK'
    BY <1>0, <1>nm DEF TypeOK, BMessage
  <1>2. bmsgsFinite'
    <2>1. 1bOr2bMsgs' \subseteq 1bOr2bMsgs \cup {[type |-> "1a", bal |-> self]}
      BY <1>0 DEF 1bOr2bMsgs
    <2>2. IsFiniteSet(1bOr2bMsgs \cup {[type |-> "1a", bal |-> self]})
      BY SingletonSetFinite, UnionOfFiniteSetsFinite DEF bmsgsFinite
    <2> QED
      BY <2>1, <2>2, SubsetOfFiniteSetFinite DEF bmsgsFinite
  <1>3. 1bInv1'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "1b", m.acc \in Acceptor,
                        NEW r \in m.m2av
                 PROVE  [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF 1bInv1
    <2>1. m \in bmsgs
      BY <1>0
    <2>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF 1bInv1
    <2> QED
      BY <2>2, <1>m
  <1>4. 1bInv2'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "1b", m2.type = "1b",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 1bInv2
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1 DEF 1bInv2
  <1>5. maxBalInv'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type \in {"1b","2av","2b"}, m.acc \in Acceptor
                 PROVE  m.bal =< maxBal'[m.acc]
      BY DEF maxBalInv
    <2>1. m \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1, <1>0 DEF maxBalInv
  <1>6. 2avInv1'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "2av", m2.type = "2av",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 2avInv1
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1 DEF 2avInv1
  <1>7. 2avInv2'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  \E r \in 2avSent'[m.acc] : r.val = m.val /\ r.bal >= m.bal
      BY DEF 2avInv2
    <2>1. m \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1, <1>0 DEF 2avInv2
  <1>8. 2avInv3'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs'
      BY DEF 2avInv3
    <2>1. m \in bmsgs
      BY <1>0
    <2>2. [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs
      BY <2>1 DEF 2avInv3
    <2> QED
      BY <2>2, <1>m
  <1>9. accInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor, NEW r \in 2avSent'[a]
                 PROVE  /\ r.bal =< maxBal'[a]
                        /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF accInv
    <2>1. r \in 2avSent[a]
      BY <1>0
    <2>2. r.bal =< maxBal[a] /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF accInv
    <2> QED
      BY <2>2, <1>0, <1>m
  <1>10. knowsSentInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  knowsSent'[a] \subseteq (msgsOfType("1b"))'
      BY DEF knowsSentInv
    <2>1. knowsSent[a] \subseteq msgsOfType("1b")
      BY DEF knowsSentInv
    <2>2. msgsOfType("1b") \subseteq (msgsOfType("1b"))'
      BY <1>sub DEF msgsOfType
    <2> QED
      BY <2>1, <2>2, <1>0
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

LEMMA LemL2 ==
  ASSUME Inv, NEW self \in Ballot, LL2(self)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv
  <1>0. PICK S \in SUBSET [type : {"1c"}, bal : {self}, val : Value] :
              /\ bmsgs' = bmsgs \cup S
              /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVVal' = maxVVal
              /\ 2avSent' = 2avSent /\ knowsSent' = knowsSent
    BY DEF LL2
  <1>type. \A mm \in S : mm.type = "1c"
    BY <1>0
  <1>sub. bmsgs \subseteq bmsgs'
    BY <1>0
  <1>sub2. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    BY <1>0
  <1>m. msgs \subseteq msgs'
    BY <1>sub, <1>sub2, MsgsMonotone
  <1>1. TypeOK'
    BY <1>0 DEF TypeOK, BMessage, 1cMessage
  <1>2. bmsgsFinite'
    <2>1. 1bOr2bMsgs' \subseteq 1bOr2bMsgs
      BY <1>0, <1>type DEF 1bOr2bMsgs
    <2> QED
      BY <2>1, SubsetOfFiniteSetFinite DEF bmsgsFinite
  <1>3. 1bInv1'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "1b", m.acc \in Acceptor,
                        NEW r \in m.m2av
                 PROVE  [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF 1bInv1
    <2>1. m \in bmsgs
      BY <1>0, <1>type
    <2>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF 1bInv1
    <2> QED
      BY <2>2, <1>m
  <1>4. 1bInv2'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "1b", m2.type = "1b",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 1bInv2
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0, <1>type
    <2> QED
      BY <2>1 DEF 1bInv2
  <1>5. maxBalInv'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type \in {"1b","2av","2b"}, m.acc \in Acceptor
                 PROVE  m.bal =< maxBal'[m.acc]
      BY DEF maxBalInv
    <2>1. m \in bmsgs
      BY <1>0, <1>type
    <2> QED
      BY <2>1, <1>0 DEF maxBalInv
  <1>6. 2avInv1'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "2av", m2.type = "2av",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 2avInv1
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0, <1>type
    <2> QED
      BY <2>1 DEF 2avInv1
  <1>7. 2avInv2'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  \E r \in 2avSent'[m.acc] : r.val = m.val /\ r.bal >= m.bal
      BY DEF 2avInv2
    <2>1. m \in bmsgs
      BY <1>0, <1>type
    <2> QED
      BY <2>1, <1>0 DEF 2avInv2
  <1>8. 2avInv3'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs'
      BY DEF 2avInv3
    <2>1. m \in bmsgs
      BY <1>0, <1>type
    <2>2. [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs
      BY <2>1 DEF 2avInv3
    <2> QED
      BY <2>2, <1>m
  <1>9. accInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor, NEW r \in 2avSent'[a]
                 PROVE  /\ r.bal =< maxBal'[a]
                        /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF accInv
    <2>1. r \in 2avSent[a]
      BY <1>0
    <2>2. r.bal =< maxBal[a] /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF accInv
    <2> QED
      BY <2>2, <1>0, <1>m
  <1>10. knowsSentInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  knowsSent'[a] \subseteq (msgsOfType("1b"))'
      BY DEF knowsSentInv
    <2>1. knowsSent[a] \subseteq msgsOfType("1b")
      BY DEF knowsSentInv
    <2>2. msgsOfType("1b") \subseteq (msgsOfType("1b"))'
      BY <1>sub DEF msgsOfType
    <2> QED
      BY <2>1, <2>2, <1>0
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

LEMMA LemF ==
  ASSUME Inv, NEW self \in FakeAcceptor, facceptor(self)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv
  <1>0. PICK mfa \in {mm \in 1bMessage \cup 2avMessage \cup 2bMessage : mm.acc = self} :
              /\ bmsgs' = bmsgs \cup {mfa}
              /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVVal' = maxVVal
              /\ 2avSent' = 2avSent /\ knowsSent' = knowsSent
    BY DEF facceptor
  <1>acc. mfa.acc = self /\ self \notin Acceptor
    BY <1>0, BQA
  <1>bm. mfa \in BMessage
    BY <1>0 DEF BMessage
  <1>sub. bmsgs \subseteq bmsgs'
    BY <1>0
  <1>sub2. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    BY <1>0
  <1>m. msgs \subseteq msgs'
    BY <1>sub, <1>sub2, MsgsMonotone
  <1>1. TypeOK'
    BY <1>0, <1>bm DEF TypeOK
  <1>2. bmsgsFinite'
    <2>1. 1bOr2bMsgs' \subseteq 1bOr2bMsgs \cup {mfa}
      BY <1>0 DEF 1bOr2bMsgs
    <2>2. IsFiniteSet(1bOr2bMsgs \cup {mfa})
      BY SingletonSetFinite, UnionOfFiniteSetsFinite DEF bmsgsFinite
    <2> QED
      BY <2>1, <2>2, SubsetOfFiniteSetFinite DEF bmsgsFinite
  <1>3. 1bInv1'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "1b", m.acc \in Acceptor,
                        NEW r \in m.m2av
                 PROVE  [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF 1bInv1
    <2>1. m \in bmsgs
      BY <1>0, <1>acc
    <2>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF 1bInv1
    <2> QED
      BY <2>2, <1>m
  <1>4. 1bInv2'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "1b", m2.type = "1b",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 1bInv2
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0, <1>acc
    <2> QED
      BY <2>1 DEF 1bInv2
  <1>5. maxBalInv'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type \in {"1b","2av","2b"}, m.acc \in Acceptor
                 PROVE  m.bal =< maxBal'[m.acc]
      BY DEF maxBalInv
    <2>1. m \in bmsgs
      BY <1>0, <1>acc
    <2> QED
      BY <2>1, <1>0 DEF maxBalInv
  <1>6. 2avInv1'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "2av", m2.type = "2av",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 2avInv1
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0, <1>acc
    <2> QED
      BY <2>1 DEF 2avInv1
  <1>7. 2avInv2'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  \E r \in 2avSent'[m.acc] : r.val = m.val /\ r.bal >= m.bal
      BY DEF 2avInv2
    <2>1. m \in bmsgs
      BY <1>0, <1>acc
    <2> QED
      BY <2>1, <1>0 DEF 2avInv2
  <1>8. 2avInv3'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs'
      BY DEF 2avInv3
    <2>1. m \in bmsgs
      BY <1>0, <1>acc
    <2>2. [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs
      BY <2>1 DEF 2avInv3
    <2> QED
      BY <2>2, <1>m
  <1>9. accInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor, NEW r \in 2avSent'[a]
                 PROVE  /\ r.bal =< maxBal'[a]
                        /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF accInv
    <2>1. r \in 2avSent[a]
      BY <1>0
    <2>2. r.bal =< maxBal[a] /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF accInv
    <2> QED
      BY <2>2, <1>0, <1>m
  <1>10. knowsSentInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  knowsSent'[a] \subseteq (msgsOfType("1b"))'
      BY DEF knowsSentInv
    <2>1. knowsSent[a] \subseteq msgsOfType("1b")
      BY DEF knowsSentInv
    <2>2. msgsOfType("1b") \subseteq (msgsOfType("1b"))'
      BY <1>sub DEF msgsOfType
    <2> QED
      BY <2>1, <2>2, <1>0
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

A1(self, b) ==
  /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ bmsgs' = (bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                            m2av |-> 2avSent[self],
                            mbal |-> maxVBal[self], mval |-> maxVVal[self]]})
  /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>

LEMMA LemA1 ==
  ASSUME Inv, NEW self \in Acceptor, NEW b \in Ballot, A1(self, b)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv, Ballot
  <1> DEFINE nb == [type  |-> "1b", bal |-> b, acc |-> self,
                    m2av |-> 2avSent[self],
                    mbal |-> maxVBal[self], mval |-> maxVVal[self]]
  <1>0. /\ b > maxBal[self]
        /\ maxBal' = [maxBal EXCEPT ![self] = b]
        /\ bmsgs' = bmsgs \cup {nb}
        /\ maxVBal' = maxVBal /\ maxVVal' = maxVVal
        /\ 2avSent' = 2avSent /\ knowsSent' = knowsSent
    BY DEF A1
  <1>arith. maxBal[self] < b /\ b \in Nat /\ maxBal[self] \in Nat \cup {-1}
    BY <1>0 DEF TypeOK
  <1>old. \A mm \in bmsgs : (mm.type \in {"1b","2av","2b"} /\ mm.acc \in Acceptor) =>
              (mm.bal \in Nat /\ mm.bal =< maxBal[mm.acc])
    <2> SUFFICES ASSUME NEW mm \in bmsgs, mm.type \in {"1b","2av","2b"}, mm.acc \in Acceptor
                 PROVE  mm.bal \in Nat /\ mm.bal =< maxBal[mm.acc]
      OBVIOUS
    <2>1. mm.bal =< maxBal[mm.acc]
      BY maxBalInv DEF maxBalInv
    <2>2. mm.bal \in Nat
      BY MsgTypeLemma DEF 1bMessage, 2avMessage, 2bMessage
    <2> QED
      BY <2>1, <2>2
  <1>sub. bmsgs \subseteq bmsgs'
    BY <1>0
  <1>sub2. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    BY <1>0
  <1>m. msgs \subseteq msgs'
    BY <1>sub, <1>sub2, MsgsMonotone
  <1>maxb. \A a \in Acceptor : maxBal'[a] = (IF a = self THEN b ELSE maxBal[a])
    BY <1>0 DEF TypeOK
  <1>1. TypeOK'
    <2>1. nb \in 1bMessage
      BY <1>0 DEF TypeOK, 1bMessage, ByzAcceptor
    <2> QED
      BY <1>0, <2>1 DEF TypeOK, BMessage
  <1>2. bmsgsFinite'
    <2>1. 1bOr2bMsgs' \subseteq 1bOr2bMsgs \cup {nb}
      BY <1>0 DEF 1bOr2bMsgs
    <2>2. IsFiniteSet(1bOr2bMsgs \cup {nb})
      BY SingletonSetFinite, UnionOfFiniteSetsFinite DEF bmsgsFinite
    <2> QED
      BY <2>1, <2>2, SubsetOfFiniteSetFinite DEF bmsgsFinite
  <1>3. 1bInv1'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "1b", m.acc \in Acceptor,
                        NEW r \in m.m2av
                 PROVE  [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF 1bInv1
    <2>1. CASE m \in bmsgs
      <3>1. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
        BY <2>1 DEF 1bInv1
      <3> QED
        BY <3>1, <1>m
    <2>2. CASE m = nb
      <3>1. r \in 2avSent[self]
        BY <2>2
      <3>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
        BY <3>1, accInv DEF accInv
      <3> QED
        BY <3>2, <1>m
    <2> QED
      BY <2>1, <2>2, <1>0
  <1>4. 1bInv2'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "1b", m2.type = "1b",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 1bInv2
    <2>1. CASE m1 \in bmsgs /\ m2 \in bmsgs
      BY <2>1 DEF 1bInv2
    <2>2. CASE m1 = nb
      <3>1. m2.acc = self /\ m2.bal = b
        BY <2>2
      <3>2. m2 \notin bmsgs
        <4> SUFFICES ASSUME m2 \in bmsgs PROVE FALSE
          OBVIOUS
        <4>1. m2.bal \in Nat /\ m2.bal =< maxBal[self]
          BY <1>old, <3>1
        <4> QED
          BY <4>1, <3>1, <1>arith
      <3>3. m2 = nb
        BY <3>2, <1>0
      <3> QED
        BY <2>2, <3>3
    <2>3. CASE m1 \in bmsgs /\ m2 = nb
      <3>1. m1.acc = self /\ m1.bal = b
        BY <2>3
      <3>2. m1.bal \in Nat /\ m1.bal =< maxBal[self]
        BY <1>old, <3>1, <2>3
      <3> QED
        BY <3>2, <3>1, <1>arith
    <2> QED
      BY <2>1, <2>2, <2>3, <1>0
  <1>5. maxBalInv'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type \in {"1b","2av","2b"}, m.acc \in Acceptor
                 PROVE  m.bal =< maxBal'[m.acc]
      BY DEF maxBalInv
    <2>1. CASE m \in bmsgs
      <3>1. m.bal \in Nat /\ m.bal =< maxBal[m.acc]
        BY <2>1, <1>old
      <3> QED
        BY <3>1, <1>maxb, <1>arith
    <2>2. CASE m = nb
      <3>1. m.acc = self /\ m.bal = b
        BY <2>2
      <3> QED
        BY <3>1, <1>maxb, <1>arith
    <2> QED
      BY <2>1, <2>2, <1>0
  <1>6. 2avInv1'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "2av", m2.type = "2av",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 2avInv1
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1 DEF 2avInv1
  <1>7. 2avInv2'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  \E r \in 2avSent'[m.acc] : r.val = m.val /\ r.bal >= m.bal
      BY DEF 2avInv2
    <2>1. m \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1, <1>0 DEF 2avInv2
  <1>8. 2avInv3'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs'
      BY DEF 2avInv3
    <2>1. m \in bmsgs
      BY <1>0
    <2>2. [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs
      BY <2>1 DEF 2avInv3
    <2> QED
      BY <2>2, <1>m
  <1>9. accInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor, NEW r \in 2avSent'[a]
                 PROVE  /\ r.bal =< maxBal'[a]
                        /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF accInv
    <2>1. r \in 2avSent[a]
      BY <1>0
    <2>2. r.bal =< maxBal[a] /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1, accInv DEF accInv
    <2>3. r.bal \in Nat
      BY <2>1 DEF TypeOK
    <2>4. r.bal =< maxBal'[a]
      BY <2>2, <2>3, <1>maxb, <1>arith
    <2> QED
      BY <2>2, <2>4, <1>m
  <1>10. knowsSentInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  knowsSent'[a] \subseteq (msgsOfType("1b"))'
      BY DEF knowsSentInv
    <2>1. knowsSent[a] \subseteq msgsOfType("1b")
      BY DEF knowsSentInv
    <2>2. msgsOfType("1b") \subseteq (msgsOfType("1b"))'
      BY <1>sub DEF msgsOfType
    <2> QED
      BY <2>1, <2>2, <1>0
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

A2(self, b) ==
  /\ /\ maxBal[self] =< b
     /\ \A r \in 2avSent[self] : r.bal < b
  /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
       /\ bmsgs' = (bmsgs \cup
                     {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]})
       /\ 2avSent' = [2avSent EXCEPT ![self] = {r \in 2avSent[self] : r.val # m.val}
                                                 \cup {[val |-> m.val, bal |-> b]}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>

LEMMA LemA2 ==
  ASSUME Inv, NEW self \in Acceptor, NEW b \in Ballot, A2(self, b)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv, Ballot
  <1>0. PICK mc \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)} :
              /\ bmsgs' = bmsgs \cup {[type |-> "2av", bal |-> b, val |-> mc.val, acc |-> self]}
              /\ 2avSent' = [2avSent EXCEPT ![self] = {r \in 2avSent[self] : r.val # mc.val}
                                                        \cup {[val |-> mc.val, bal |-> b]}]
              /\ maxBal' = [maxBal EXCEPT ![self] = b]
              /\ maxVBal' = maxVBal /\ maxVVal' = maxVVal /\ knowsSent' = knowsSent
    BY DEF A2
  <1> DEFINE na == [type |-> "2av", bal |-> b, val |-> mc.val, acc |-> self]
  <1>cond. maxBal[self] =< b /\ (\A r \in 2avSent[self] : r.bal < b)
    BY DEF A2
  <1>mc1. mc \in bmsgs /\ mc.type = "1c" /\ mc.bal = b /\ KnowsSafeAt(self, b, mc.val)
    BY <1>0 DEF sentMsgs
  <1>mc2. mc.val \in Value /\ mc = [type |-> "1c", bal |-> b, val |-> mc.val]
    BY <1>mc1, MsgTypeLemma DEF 1cMessage
  <1>arith. b \in Nat /\ maxBal[self] \in Nat \cup {-1} /\ maxBal[self] =< b
    BY <1>cond DEF TypeOK
  <1>old. \A mm \in bmsgs : (mm.type \in {"1b","2av","2b"} /\ mm.acc \in Acceptor) =>
              (mm.bal \in Nat /\ mm.bal =< maxBal[mm.acc])
    <2> SUFFICES ASSUME NEW mm \in bmsgs, mm.type \in {"1b","2av","2b"}, mm.acc \in Acceptor
                 PROVE  mm.bal \in Nat /\ mm.bal =< maxBal[mm.acc]
      OBVIOUS
    <2>1. mm.bal =< maxBal[mm.acc]
      BY maxBalInv DEF maxBalInv
    <2>2. mm.bal \in Nat
      BY MsgTypeLemma DEF 1bMessage, 2avMessage, 2bMessage
    <2> QED
      BY <2>1, <2>2
  <1>sub. bmsgs \subseteq bmsgs'
    BY <1>0
  <1>sub2. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    BY <1>0
  <1>m. msgs \subseteq msgs'
    BY <1>sub, <1>sub2, MsgsMonotone
  <1>maxb. \A a \in Acceptor : maxBal'[a] = (IF a = self THEN b ELSE maxBal[a])
    BY <1>0 DEF TypeOK
  <1>sent. /\ \A a \in Acceptor : a # self => 2avSent'[a] = 2avSent[a]
           /\ 2avSent'[self] = {r \in 2avSent[self] : r.val # mc.val} \cup {[val |-> mc.val, bal |-> b]}
    BY <1>0 DEF TypeOK
  <1>1c. [type |-> "1c", bal |-> b, val |-> mc.val] \in msgs'
    <2>1. mc \in msgsOfType("1c")
      BY <1>mc1 DEF msgsOfType
    <2>2. \E aa \in Acceptor : KnowsSafeAt(aa, mc.bal, mc.val)
      BY <1>mc1
    <2>3. mc \in 1cmsgs
      BY <2>1, <2>2 DEF 1cmsgs
    <2>4. mc \in msgs
      BY <2>3 DEF msgs
    <2> QED
      BY <2>4, <1>m, <1>mc2
  <1>uniq2av. \A mm \in bmsgs : ~(mm.type = "2av" /\ mm.acc = self /\ mm.bal = b)
    <2> SUFFICES ASSUME NEW mm \in bmsgs, mm.type = "2av", mm.acc = self, mm.bal = b
                 PROVE  FALSE
      OBVIOUS
    <2>1. \E r \in 2avSent[self] : r.val = mm.val /\ r.bal >= mm.bal
      BY 2avInv2 DEF 2avInv2
    <2>2. PICK r \in 2avSent[self] : r.bal >= b
      BY <2>1
    <2>3. r.bal < b
      BY <2>2, <1>cond
    <2>4. r.bal \in Nat
      BY <2>2 DEF TypeOK
    <2> QED
      BY <2>2, <2>3, <2>4, <1>arith
  <1>1. TypeOK'
    <2>1. na \in 2avMessage
      BY <1>mc2 DEF 2avMessage, ByzAcceptor
    <2>2. {r \in 2avSent[self] : r.val # mc.val} \cup {[val |-> mc.val, bal |-> b]}
            \in SUBSET [val : Value, bal : Ballot]
      BY <1>mc2 DEF TypeOK
    <2> QED
      BY <1>0, <2>1, <2>2 DEF TypeOK, BMessage
  <1>2. bmsgsFinite'
    <2>1. 1bOr2bMsgs' \subseteq 1bOr2bMsgs \cup {na}
      BY <1>0 DEF 1bOr2bMsgs
    <2>2. IsFiniteSet(1bOr2bMsgs \cup {na})
      BY SingletonSetFinite, UnionOfFiniteSetsFinite DEF bmsgsFinite
    <2> QED
      BY <2>1, <2>2, SubsetOfFiniteSetFinite DEF bmsgsFinite
  <1>3. 1bInv1'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "1b", m.acc \in Acceptor,
                        NEW r \in m.m2av
                 PROVE  [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF 1bInv1
    <2>1. m \in bmsgs
      BY <1>0
    <2>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF 1bInv1
    <2> QED
      BY <2>2, <1>m
  <1>4. 1bInv2'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "1b", m2.type = "1b",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 1bInv2
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1 DEF 1bInv2
  <1>5. maxBalInv'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type \in {"1b","2av","2b"}, m.acc \in Acceptor
                 PROVE  m.bal =< maxBal'[m.acc]
      BY DEF maxBalInv
    <2>1. CASE m \in bmsgs
      <3>1. m.bal \in Nat /\ m.bal =< maxBal[m.acc]
        BY <2>1, <1>old
      <3> QED
        BY <3>1, <1>maxb, <1>arith
    <2>2. CASE m = na
      <3>1. m.acc = self /\ m.bal = b
        BY <2>2
      <3> QED
        BY <3>1, <1>maxb, <1>arith
    <2> QED
      BY <2>1, <2>2, <1>0
  <1>6. 2avInv1'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "2av", m2.type = "2av",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 2avInv1
    <2>1. CASE m1 \in bmsgs /\ m2 \in bmsgs
      BY <2>1 DEF 2avInv1
    <2>2. CASE m1 = na
      <3>1. m2.acc = self /\ m2.bal = b
        BY <2>2
      <3>2. m2 \notin bmsgs
        BY <1>uniq2av, <3>1
      <3>3. m2 = na
        BY <3>2, <1>0
      <3> QED
        BY <2>2, <3>3
    <2>3. CASE m1 \in bmsgs /\ m2 = na
      <3>1. m1.acc = self /\ m1.bal = b
        BY <2>3
      <3>2. FALSE
        BY <1>uniq2av, <3>1, <2>3
      <3> QED
        BY <3>2
    <2> QED
      BY <2>1, <2>2, <2>3, <1>0
  <1>7. 2avInv2'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  \E r \in 2avSent'[m.acc] : r.val = m.val /\ r.bal >= m.bal
      BY DEF 2avInv2
    <2>na. CASE m = na
      <3>1. [val |-> mc.val, bal |-> b] \in 2avSent'[self]
        BY <1>sent
      <3>2. m.acc = self /\ m.val = mc.val /\ m.bal = b
        BY <2>na
      <3> QED
        BY <3>1, <3>2
    <2>old. CASE m \in bmsgs
      <3>0. PICK r \in 2avSent[m.acc] : r.val = m.val /\ r.bal >= m.bal
        BY <2>old, 2avInv2 DEF 2avInv2
      <3>1. CASE m.acc # self
        <4>1. 2avSent'[m.acc] = 2avSent[m.acc]
          BY <1>sent, <3>1
        <4> QED
          BY <3>0, <4>1
      <3>2. CASE m.acc = self
        <4>1. CASE r.val # mc.val
          <5>1. r \in 2avSent'[self]
            BY <3>0, <4>1, <1>sent, <3>2
          <5> QED
            BY <5>1, <3>0, <3>2
        <4>2. CASE r.val = mc.val
          <5>1. m.val = mc.val
            BY <3>0, <4>2
          <5>2. m.bal =< b
            <6>1. m.bal \in Nat /\ m.bal =< maxBal[self]
              BY <2>old, <3>2, <1>old
            <6> QED
              BY <6>1, <1>arith
          <5>3. [val |-> mc.val, bal |-> b] \in 2avSent'[self]
            BY <1>sent
          <5> QED
            BY <5>1, <5>2, <5>3, <3>2
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2
    <2> QED
      BY <2>na, <2>old, <1>0
  <1>8. 2avInv3'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs'
      BY DEF 2avInv3
    <2>na. CASE m = na
      <3>1. m.bal = b /\ m.val = mc.val
        BY <2>na
      <3> QED
        BY <3>1, <1>1c
    <2>old. CASE m \in bmsgs
      <3>1. [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs
        BY <2>old DEF 2avInv3
      <3> QED
        BY <3>1, <1>m
    <2> QED
      BY <2>na, <2>old, <1>0
  <1>9. accInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor, NEW r \in 2avSent'[a]
                 PROVE  /\ r.bal =< maxBal'[a]
                        /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF accInv
    <2>1. CASE a # self
      <3>1. 2avSent'[a] = 2avSent[a] /\ maxBal'[a] = maxBal[a]
        BY <1>sent, <1>maxb, <2>1
      <3>2. r \in 2avSent[a]
        BY <3>1
      <3>3. r.bal =< maxBal[a] /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
        BY <3>2, accInv DEF accInv
      <3> QED
        BY <3>3, <3>1, <1>m
    <2>2. CASE a = self
      <3>0. r \in {rr \in 2avSent[self] : rr.val # mc.val} \/ r = [val |-> mc.val, bal |-> b]
        BY <2>2, <1>sent
      <3>1. maxBal'[self] = b
        BY <1>maxb
      <3>2. CASE r \in {rr \in 2avSent[self] : rr.val # mc.val}
        <4>1. r \in 2avSent[self]
          BY <3>2
        <4>2. r.bal =< maxBal[self] /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
          BY <4>1, accInv DEF accInv
        <4>3. r.bal \in Nat
          BY <4>1 DEF TypeOK
        <4>4. r.bal =< b
          BY <4>2, <4>3, <1>arith
        <4> QED
          BY <4>4, <4>2, <3>1, <2>2, <1>m
      <3>3. CASE r = [val |-> mc.val, bal |-> b]
        <4>1. r.bal = b /\ r.val = mc.val
          BY <3>3
        <4>2. r.bal =< maxBal'[a]
          BY <4>1, <3>1, <2>2, <1>arith
        <4>3. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
          BY <4>1, <1>1c
        <4> QED
          BY <4>2, <4>3
      <3> QED
        BY <3>0, <3>2, <3>3
    <2> QED
      BY <2>1, <2>2
  <1>10. knowsSentInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  knowsSent'[a] \subseteq (msgsOfType("1b"))'
      BY DEF knowsSentInv
    <2>1. knowsSent[a] \subseteq msgsOfType("1b")
      BY DEF knowsSentInv
    <2>2. msgsOfType("1b") \subseteq (msgsOfType("1b"))'
      BY <1>sub DEF msgsOfType
    <2> QED
      BY <2>1, <2>2, <1>0
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

A3(self, b) ==
  /\ maxBal[self] =< b
  /\ \E v \in {vv \in Value :
                 \E Q \in ByzQuorum :
                    \A aa \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                     /\ m.acc = aa}:
       /\ bmsgs' = (bmsgs \cup
                     {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
       /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
  /\ UNCHANGED <<2avSent, knowsSent>>

LEMMA LemA3 ==
  ASSUME Inv, NEW self \in Acceptor, NEW b \in Ballot, A3(self, b)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv, Ballot
  <1>0. PICK v \in {vv \in Value :
                      \E Q \in ByzQuorum :
                         \A aa \in Q :
                            \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                          /\ m.acc = aa} :
              /\ bmsgs' = bmsgs \cup {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
              /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
              /\ maxBal' = [maxBal EXCEPT ![self] = b]
              /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
              /\ 2avSent' = 2avSent /\ knowsSent' = knowsSent
    BY DEF A3
  <1> DEFINE nb2 == [type |-> "2b", acc |-> self, bal |-> b, val |-> v]
  <1>v. v \in Value
    BY <1>0
  <1>cond. maxBal[self] =< b
    BY DEF A3
  <1>arith. b \in Nat /\ maxBal[self] \in Nat \cup {-1} /\ maxBal[self] =< b
    BY <1>cond DEF TypeOK
  <1>old. \A mm \in bmsgs : (mm.type \in {"1b","2av","2b"} /\ mm.acc \in Acceptor) =>
              (mm.bal \in Nat /\ mm.bal =< maxBal[mm.acc])
    <2> SUFFICES ASSUME NEW mm \in bmsgs, mm.type \in {"1b","2av","2b"}, mm.acc \in Acceptor
                 PROVE  mm.bal \in Nat /\ mm.bal =< maxBal[mm.acc]
      OBVIOUS
    <2>1. mm.bal =< maxBal[mm.acc]
      BY maxBalInv DEF maxBalInv
    <2>2. mm.bal \in Nat
      BY MsgTypeLemma DEF 1bMessage, 2avMessage, 2bMessage
    <2> QED
      BY <2>1, <2>2
  <1>sub. bmsgs \subseteq bmsgs'
    BY <1>0
  <1>sub2. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    BY <1>0
  <1>m. msgs \subseteq msgs'
    BY <1>sub, <1>sub2, MsgsMonotone
  <1>maxb. \A a \in Acceptor : maxBal'[a] = (IF a = self THEN b ELSE maxBal[a])
    BY <1>0 DEF TypeOK
  <1>1. TypeOK'
    <2>1. nb2 \in 2bMessage
      BY <1>v DEF 2bMessage, ByzAcceptor
    <2> QED
      BY <1>0, <1>v, <2>1 DEF TypeOK, BMessage
  <1>2. bmsgsFinite'
    <2>1. 1bOr2bMsgs' \subseteq 1bOr2bMsgs \cup {nb2}
      BY <1>0 DEF 1bOr2bMsgs
    <2>2. IsFiniteSet(1bOr2bMsgs \cup {nb2})
      BY SingletonSetFinite, UnionOfFiniteSetsFinite DEF bmsgsFinite
    <2> QED
      BY <2>1, <2>2, SubsetOfFiniteSetFinite DEF bmsgsFinite
  <1>3. 1bInv1'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "1b", m.acc \in Acceptor,
                        NEW r \in m.m2av
                 PROVE  [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF 1bInv1
    <2>1. m \in bmsgs
      BY <1>0
    <2>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF 1bInv1
    <2> QED
      BY <2>2, <1>m
  <1>4. 1bInv2'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "1b", m2.type = "1b",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 1bInv2
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1 DEF 1bInv2
  <1>5. maxBalInv'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type \in {"1b","2av","2b"}, m.acc \in Acceptor
                 PROVE  m.bal =< maxBal'[m.acc]
      BY DEF maxBalInv
    <2>1. CASE m \in bmsgs
      <3>1. m.bal \in Nat /\ m.bal =< maxBal[m.acc]
        BY <2>1, <1>old
      <3> QED
        BY <3>1, <1>maxb, <1>arith
    <2>2. CASE m = nb2
      <3>1. m.acc = self /\ m.bal = b
        BY <2>2
      <3> QED
        BY <3>1, <1>maxb, <1>arith
    <2> QED
      BY <2>1, <2>2, <1>0
  <1>6. 2avInv1'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "2av", m2.type = "2av",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 2avInv1
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1 DEF 2avInv1
  <1>7. 2avInv2'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  \E r \in 2avSent'[m.acc] : r.val = m.val /\ r.bal >= m.bal
      BY DEF 2avInv2
    <2>1. m \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1, <1>0 DEF 2avInv2
  <1>8. 2avInv3'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs'
      BY DEF 2avInv3
    <2>1. m \in bmsgs
      BY <1>0
    <2>2. [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs
      BY <2>1 DEF 2avInv3
    <2> QED
      BY <2>2, <1>m
  <1>9. accInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor, NEW r \in 2avSent'[a]
                 PROVE  /\ r.bal =< maxBal'[a]
                        /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF accInv
    <2>1. r \in 2avSent[a]
      BY <1>0
    <2>2. r.bal =< maxBal[a] /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1, accInv DEF accInv
    <2>3. r.bal \in Nat
      BY <2>1 DEF TypeOK
    <2>4. r.bal =< maxBal'[a]
      BY <2>2, <2>3, <1>maxb, <1>arith
    <2> QED
      BY <2>2, <2>4, <1>m
  <1>10. knowsSentInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  knowsSent'[a] \subseteq (msgsOfType("1b"))'
      BY DEF knowsSentInv
    <2>1. knowsSent[a] \subseteq msgsOfType("1b")
      BY DEF knowsSentInv
    <2>2. msgsOfType("1b") \subseteq (msgsOfType("1b"))'
      BY <1>sub DEF msgsOfType
    <2> QED
      BY <2>1, <2>2, <1>0
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

A4(self, b) ==
  /\ \E S \in SUBSET sentMsgs("1b", b):
        knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
  /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

LEMMA LemA4 ==
  ASSUME Inv, NEW self \in Acceptor, NEW b \in Ballot, A4(self, b)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv
  <1>0. PICK S \in SUBSET sentMsgs("1b", b) :
              /\ knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
              /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVVal' = maxVVal
              /\ 2avSent' = 2avSent /\ bmsgs' = bmsgs
    BY DEF A4
  <1>S1b. S \subseteq msgsOfType("1b") /\ S \subseteq 1bMessage
    <2>1. sentMsgs("1b", b) \subseteq msgsOfType("1b")
      BY DEF sentMsgs, msgsOfType
    <2>2. sentMsgs("1b", b) \subseteq 1bMessage
      BY MsgTypeLemma DEF sentMsgs
    <2> QED
      BY <1>0, <2>1, <2>2
  <1>ks. \A a \in Acceptor :
            knowsSent'[a] = (IF a = self THEN knowsSent[self] \cup S ELSE knowsSent[a])
    BY <1>0 DEF TypeOK
  <1>sub. bmsgs \subseteq bmsgs'
    BY <1>0
  <1>sub2. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    BY <1>ks
  <1>m. msgs \subseteq msgs'
    BY <1>sub, <1>sub2, MsgsMonotone
  <1>1. TypeOK'
    BY <1>0, <1>S1b DEF TypeOK
  <1>2. bmsgsFinite'
    BY <1>0 DEF bmsgsFinite, 1bOr2bMsgs
  <1>3. 1bInv1'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "1b", m.acc \in Acceptor,
                        NEW r \in m.m2av
                 PROVE  [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF 1bInv1
    <2>1. m \in bmsgs
      BY <1>0
    <2>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1 DEF 1bInv1
    <2> QED
      BY <2>2, <1>m
  <1>4. 1bInv2'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "1b", m2.type = "1b",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 1bInv2
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1 DEF 1bInv2
  <1>5. maxBalInv'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type \in {"1b","2av","2b"}, m.acc \in Acceptor
                 PROVE  m.bal =< maxBal'[m.acc]
      BY DEF maxBalInv
    <2>1. m \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1, <1>0 DEF maxBalInv
  <1>6. 2avInv1'
    <2> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                        m1.type = "2av", m2.type = "2av",
                        m1.acc \in Acceptor, m1.acc = m2.acc, m1.bal = m2.bal
                 PROVE  m1 = m2
      BY DEF 2avInv1
    <2>1. m1 \in bmsgs /\ m2 \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1 DEF 2avInv1
  <1>7. 2avInv2'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  \E r \in 2avSent'[m.acc] : r.val = m.val /\ r.bal >= m.bal
      BY DEF 2avInv2
    <2>1. m \in bmsgs
      BY <1>0
    <2> QED
      BY <2>1, <1>0 DEF 2avInv2
  <1>8. 2avInv3'
    <2> SUFFICES ASSUME NEW m \in bmsgs', m.type = "2av", m.acc \in Acceptor
                 PROVE  [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs'
      BY DEF 2avInv3
    <2>1. m \in bmsgs
      BY <1>0
    <2>2. [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs
      BY <2>1 DEF 2avInv3
    <2> QED
      BY <2>2, <1>m
  <1>9. accInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor, NEW r \in 2avSent'[a]
                 PROVE  /\ r.bal =< maxBal'[a]
                        /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
      BY DEF accInv
    <2>1. r \in 2avSent[a]
      BY <1>0
    <2>2. r.bal =< maxBal[a] /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
      BY <2>1, accInv DEF accInv
    <2> QED
      BY <2>2, <1>0, <1>m
  <1>10. knowsSentInv'
    <2> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  knowsSent'[a] \subseteq (msgsOfType("1b"))'
      BY DEF knowsSentInv
    <2>1. msgsOfType("1b") = (msgsOfType("1b"))'
      BY <1>0 DEF msgsOfType
    <2>2. knowsSent[a] \subseteq msgsOfType("1b")
      BY DEF knowsSentInv
    <2>3. knowsSent'[a] \subseteq msgsOfType("1b")
      BY <1>ks, <2>2, <1>S1b
    <2> QED
      BY <2>3, <2>1
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10

THEOREM Spec => []Inv
PROOF
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <2> USE DEF Init
  <2>1. TypeOK
    BY DEF TypeOK
  <2>2. bmsgsFinite
    <3>1. 1bOr2bMsgs = {}
      BY DEF 1bOr2bMsgs
    <3> QED
      BY <3>1, EmptySetFinite DEF bmsgsFinite
  <2>3. 1bInv1
    BY DEF 1bInv1
  <2>4. 1bInv2
    BY DEF 1bInv2
  <2>5. maxBalInv
    BY DEF maxBalInv
  <2>6. 2avInv1
    BY DEF 2avInv1
  <2>7. 2avInv2
    BY DEF 2avInv2
  <2>8. 2avInv3
    BY DEF 2avInv3
  <2>9. accInv
    BY DEF accInv
  <2>10. knowsSentInv
    BY DEF knowsSentInv
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE \E self \in Acceptor : acceptor(self)
    <3>1. PICK self \in Acceptor : acceptor(self)
      BY <2>1
    <3>2. \E b \in Ballot : A1(self,b) \/ A2(self,b) \/ A3(self,b) \/ A4(self,b)
      BY <3>1 DEF acceptor, A1, A2, A3, A4
    <3>3. PICK b \in Ballot : A1(self,b) \/ A2(self,b) \/ A3(self,b) \/ A4(self,b)
      BY <3>2
    <3>4. CASE A1(self,b)
      BY <3>4, LemA1
    <3>5. CASE A2(self,b)
      BY <3>5, LemA2
    <3>6. CASE A3(self,b)
      BY <3>6, LemA3
    <3>7. CASE A4(self,b)
      BY <3>7, LemA4
    <3> QED
      BY <3>3, <3>4, <3>5, <3>6, <3>7
  <2>2. CASE \E self \in Ballot : leader(self)
    <3>1. PICK self \in Ballot : leader(self)
      BY <2>2
    <3>2. LL1(self) \/ LL2(self)
      BY <3>1 DEF leader, LL1, LL2
    <3>3. CASE LL1(self)
      BY <3>3, LemL1
    <3>4. CASE LL2(self)
      BY <3>4, LemL2
    <3> QED
      BY <3>2, <3>3, <3>4
  <2>3. CASE \E self \in FakeAcceptor : facceptor(self)
    <3>1. PICK self \in FakeAcceptor : facceptor(self)
      BY <2>3
    <3> QED
      BY <3>1, LemF
  <2>4. CASE UNCHANGED vars
    BY <2>4, LemStutter
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

==============================================================================

