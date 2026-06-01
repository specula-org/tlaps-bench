
---------------------------- MODULE BPConProof_P_Spec ------------------------------

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

1bMessage == 

  [type : {"1b"}, bal : Ballot, 
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

2avMessage ==

   [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]

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

MaxBallot(S) ==  
  IF S = {} THEN -1
            ELSE CHOOSE mb \in S : \A x \in S : mb  >= x

AXIOM FiniteSetHasMax == 
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

1bOr2bMsgs == {m \in bmsgs : m.type \in {"1b", "2b"}}

PmaxBal == [a \in Acceptor |-> 
              MaxBallot({m.bal : m \in {ma \in 1bOr2bMsgs : 
                                           ma.acc = a}})]

P == INSTANCE PConProof WITH maxBal <- PmaxBal
-----------------------------------------------------------------------------

LEMMA MaxBallotEmpty == MaxBallot({}) = -1
  BY DEF MaxBallot

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
  <1> SUFFICES ASSUME NEW Q \in Quorum
               PROVE  Q # {}
    OBVIOUS
  <1>1. PICK S \in ByzQuorum : Q = S \cap Acceptor
    BY DEF Quorum
  <1>2. S \cap S \cap Acceptor # {}
    BY BQA, <1>1
  <1>3. QED
    BY <1>2, <1>1

LEMMA QuorumSubsetAcceptor == \A Q \in Quorum : Q \subseteq Acceptor
  BY DEF Quorum
-----------------------------------------------------------------------------

LEMMA InitImpliesPInit == Init => P!Init
  <1> SUFFICES ASSUME Init
               PROVE  P!Init
    OBVIOUS
  <1>1. bmsgs = {}
    BY DEF Init
  <1>2. 1bOr2bMsgs = {}
    BY <1>1 DEF 1bOr2bMsgs
  <1>3. \A a \in Acceptor : {m.bal : m \in {ma \in 1bOr2bMsgs : ma.acc = a}} = {}
    BY <1>2
  <1>4. PmaxBal = [a \in Acceptor |-> -1]
    BY <1>3, MaxBallotEmpty DEF PmaxBal
  <1>5. msgsOfType("1a") = {} /\ msgsOfType("1b") = {} /\ msgsOfType("1c") = {}
        /\ msgsOfType("2av") = {} /\ msgsOfType("2b") = {}
    BY <1>1 DEF msgsOfType
  <1>6. acceptorMsgsOfType("1b") = {} /\ acceptorMsgsOfType("2av") = {}
        /\ acceptorMsgsOfType("2b") = {}
    BY <1>5 DEF acceptorMsgsOfType
  <1>7. 1bmsgs = {}
    BY <1>6 DEF 1bmsgs
  <1>8. 1cmsgs = {}
    BY <1>5 DEF 1cmsgs
  <1>9. 2amsgs = {}
    <2>1. SUFFICES ASSUME NEW m \in [type : {"2a"}, bal : Ballot, val : Value],
                          m \in 2amsgs
                   PROVE  FALSE
      BY <2>1 DEF 2amsgs
    <2>2. PICK Q \in Quorum : \A a \in Q :
                 \E m2av \in acceptorMsgsOfType("2av") :
                    /\ m2av.acc = a
                    /\ m2av.bal = m.bal
                    /\ m2av.val = m.val
      BY <2>1 DEF 2amsgs
    <2>3. PICK a \in Q : TRUE
      BY QuorumNonEmpty
    <2>4. \E m2av \in acceptorMsgsOfType("2av") : m2av.acc = a
      BY <2>2, <2>3
    <2>5. QED
      BY <2>4, <1>6
  <1>10. msgs = {}
    BY <1>5, <1>7, <1>8, <1>9, <1>6 DEF msgs
  <1>11. None = P!None
    BY DEF None, P!None
  <1>12. maxVVal = [a \in Acceptor |-> P!None]
    BY <1>11 DEF Init
  <1>13. QED
    BY <1>4, <1>10, <1>12 DEF P!Init, Init

-----------------------------------------------------------------------------

LEMMA UnchangedImpliesPUnchanged ==
  ASSUME UNCHANGED vars
  PROVE  P!vars' = P!vars
  <1>1. bmsgs' = bmsgs
    BY DEF vars
  <1>2. knowsSent' = knowsSent
    BY DEF vars
  <1>3. maxVBal' = maxVBal /\ maxVVal' = maxVVal
    BY DEF vars
  <1>4. 1bOr2bMsgs' = 1bOr2bMsgs
    BY <1>1 DEF 1bOr2bMsgs
  <1>5. PmaxBal' = PmaxBal
    BY <1>4 DEF PmaxBal
  <1>6. msgsOfType("1a")' = msgsOfType("1a")
    BY <1>1 DEF msgsOfType
  <1>7. acceptorMsgsOfType("1b")' = acceptorMsgsOfType("1b")
        /\ acceptorMsgsOfType("2av")' = acceptorMsgsOfType("2av")
        /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    BY <1>1 DEF acceptorMsgsOfType, msgsOfType
  <1>8. 1bmsgs' = 1bmsgs
    BY <1>7 DEF 1bmsgs, 1bRestrict
  <1>9. 1cmsgs' = 1cmsgs
    BY <1>1, <1>2 DEF 1cmsgs, msgsOfType, KnowsSafeAt
  <1>10. 2amsgs' = 2amsgs
    BY <1>7 DEF 2amsgs
  <1>11. msgs' = msgs
    BY <1>6, <1>8, <1>9, <1>10, <1>7 DEF msgs
  <1>12. QED
    BY <1>5, <1>11, <1>3 DEF P!vars

-----------------------------------------------------------------------------

\* Define an inductive invariant that captures what we need
TypeOK ==
  /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
  /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
  /\ maxVVal \in [Acceptor -> Value \cup {None}]
  /\ 2avSent \in [Acceptor -> SUBSET [val : Value, bal : Ballot]]
  /\ knowsSent \in [Acceptor -> SUBSET 1bMessage]
  /\ bmsgs \in SUBSET (
       [type : {"1a"}, bal : Ballot] \cup
       1bMessage \cup
       [type : {"1c"}, bal : Ballot, val : Value] \cup
       2avMessage \cup
       2bMessage)

\* Specific invariants needed for refinement
PmaxBalProp ==
  /\ \A a \in Acceptor : PmaxBal[a] \in Ballot \cup {-1}
  /\ \A a \in Acceptor : PmaxBal[a] <= maxBal[a]

IndInv == TypeOK /\ PmaxBalProp

-----------------------------------------------------------------------------

LEMMA FakeStuttering ==
  ASSUME NEW self \in FakeAcceptor, facceptor(self)
  PROVE  P!vars' = P!vars
  <1> USE BQA, BQLA
  <1>1. self \notin Acceptor
    BY BQA
  <1>2. PICK m \in 1bMessage \cup 2avMessage \cup 2bMessage :
          /\ m.acc = self
          /\ bmsgs' = bmsgs \cup {m}
    BY DEF facceptor
  <1>3. m.acc \notin Acceptor
    BY <1>1, <1>2
  <1>4. m.type \in {"1b", "2av", "2b"}
    BY <1>2 DEF 1bMessage, 2avMessage, 2bMessage
  <1>5. UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, knowsSent>>
    BY DEF facceptor
  <1>6. \A a \in Acceptor : {ma \in 1bOr2bMsgs' : ma.acc = a} = {ma \in 1bOr2bMsgs : ma.acc = a}
    BY <1>2, <1>3 DEF 1bOr2bMsgs
  <1>7. PmaxBal' = PmaxBal
    BY <1>6 DEF PmaxBal
  <1>8. msgsOfType("1a")' = msgsOfType("1a")
        /\ msgsOfType("1c")' = msgsOfType("1c")
    BY <1>2, <1>4 DEF msgsOfType
  <1>9. acceptorMsgsOfType("1b")' = acceptorMsgsOfType("1b")
        /\ acceptorMsgsOfType("2av")' = acceptorMsgsOfType("2av")
        /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    BY <1>2, <1>3 DEF acceptorMsgsOfType, msgsOfType
  <1>10. 1bmsgs' = 1bmsgs
    BY <1>9 DEF 1bmsgs, 1bRestrict
  <1>11. knowsSent' = knowsSent
    BY <1>5
  <1>12. 1cmsgs' = 1cmsgs
    BY <1>8, <1>11 DEF 1cmsgs, KnowsSafeAt
  <1>13. 2amsgs' = 2amsgs
    BY <1>9 DEF 2amsgs
  <1>14. msgs' = msgs
    BY <1>8, <1>10, <1>12, <1>13, <1>9 DEF msgs
  <1>15. maxVBal' = maxVBal /\ maxVVal' = maxVVal
    BY <1>5
  <1>16. QED
    BY <1>7, <1>14, <1>15 DEF P!vars

LEMMA Leader1aImpliesPNext ==
  ASSUME NEW self \in Ballot,
         bmsgs' = bmsgs \cup {[type |-> "1a", bal |-> self]},
         UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, knowsSent>>
  PROVE  P!Next
  <1> DEFINE m1a == [type |-> "1a", bal |-> self]
  <1>1. m1a.type = "1a" /\ m1a.bal = self
    OBVIOUS
  <1>2. 1bOr2bMsgs' = 1bOr2bMsgs
    BY DEF 1bOr2bMsgs
  <1>3. PmaxBal' = PmaxBal
    BY <1>2 DEF PmaxBal
  <1>4. msgsOfType("1a")' = msgsOfType("1a") \cup {m1a}
    BY <1>1 DEF msgsOfType
  <1>5. msgsOfType("1c")' = msgsOfType("1c")
    BY <1>1 DEF msgsOfType
  <1>6. acceptorMsgsOfType("1b")' = acceptorMsgsOfType("1b")
        /\ acceptorMsgsOfType("2av")' = acceptorMsgsOfType("2av")
        /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    BY <1>1 DEF acceptorMsgsOfType, msgsOfType
  <1>7. 1bmsgs' = 1bmsgs
    BY <1>6 DEF 1bmsgs, 1bRestrict
  <1>8. knowsSent' = knowsSent
    OBVIOUS
  <1>9. 1cmsgs' = 1cmsgs
    BY <1>5, <1>8 DEF 1cmsgs, KnowsSafeAt
  <1>10. 2amsgs' = 2amsgs
    BY <1>6 DEF 2amsgs
  <1>11. msgs' = msgs \cup {m1a}
    BY <1>4, <1>7, <1>9, <1>10, <1>6 DEF msgs
  <1>12. maxVBal' = maxVBal /\ maxVVal' = maxVVal
    OBVIOUS
  <1>13. P!leader(self)
    <2>1. msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
      BY <1>11
    <2>2. UNCHANGED <<PmaxBal, maxVBal, maxVVal>>
      BY <1>3, <1>12
    <2>3. QED
      BY <2>1, <2>2 DEF P!leader
  <1>14. \E s \in P!Ballot : P!leader(s)
    BY <1>13 DEF P!Ballot, Ballot
  <1>15. QED
    BY <1>14 DEF P!Next

THEOREM Spec => P!Spec
  <1>1. Init => P!Init
    BY InitImpliesPInit
  <1>2. [Next]_vars => [P!Next]_P!vars
    <2> SUFFICES ASSUME [Next]_vars
                 PROVE  [P!Next]_P!vars
      OBVIOUS
    <2>1. CASE UNCHANGED vars
      BY <2>1, UnchangedImpliesPUnchanged
    <2>2. CASE Next
      <3> USE BQA, BQLA, BallotAssump
      <3>1. CASE \E s \in FakeAcceptor : facceptor(s)
        <4>1. PICK s \in FakeAcceptor : facceptor(s)
          BY <3>1
        <4>2. P!vars' = P!vars
          BY <4>1, FakeStuttering
        <4>3. QED
          BY <4>2
      <3>2. CASE \E self \in Ballot : leader(self)
        <4>1. PICK self \in Ballot : leader(self)
          BY <3>2
        <4>2. UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, knowsSent>>
          BY <4>1 DEF leader
        <4>3. CASE bmsgs' = bmsgs \cup {[type |-> "1a", bal |-> self]}
          <5>1. P!Next
            BY <4>3, <4>2, <4>1, Leader1aImpliesPNext
          <5>2. QED
            BY <5>1
        <4>4. CASE \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                     bmsgs' = bmsgs \cup S
          \* P!Phase1c or stuttering case
          <5>1. PICK S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                  bmsgs' = bmsgs \cup S
            BY <4>4
          <5>2. \A m \in S : m.type = "1c" /\ m.bal = self
            BY <5>1
          <5>3. 1bOr2bMsgs' = 1bOr2bMsgs
            BY <5>1, <5>2 DEF 1bOr2bMsgs
          <5>4. PmaxBal' = PmaxBal
            BY <5>3 DEF PmaxBal
          <5>5. msgsOfType("1a")' = msgsOfType("1a")
            BY <5>1, <5>2 DEF msgsOfType
          <5>6. acceptorMsgsOfType("1b")' = acceptorMsgsOfType("1b")
                /\ acceptorMsgsOfType("2av")' = acceptorMsgsOfType("2av")
                /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
            BY <5>1, <5>2 DEF acceptorMsgsOfType, msgsOfType
          <5>7. 1bmsgs' = 1bmsgs
            BY <5>6 DEF 1bmsgs, 1bRestrict
          <5>8. 2amsgs' = 2amsgs
            BY <5>6 DEF 2amsgs
          <5>9. knowsSent' = knowsSent
            BY <4>2
          <5>10. msgsOfType("1c")' = msgsOfType("1c") \cup S
            BY <5>1, <5>2 DEF msgsOfType
          <5> DEFINE NewS == {m \in S : \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}
          <5>11. 1cmsgs' = 1cmsgs \cup NewS
            <6>1. \A m, a : KnowsSafeAt(a, m.bal, m.val)' = KnowsSafeAt(a, m.bal, m.val)
              BY <5>9 DEF KnowsSafeAt
            <6>2. QED
              BY <5>10, <6>1 DEF 1cmsgs
          <5>12. msgs' = msgs \cup NewS
            BY <5>5, <5>7, <5>11, <5>8, <5>6 DEF msgs
          <5>13. maxVBal' = maxVBal /\ maxVVal' = maxVVal
            BY <4>2
          <5>14. CASE NewS = {}
            <6>1. msgs' = msgs
              BY <5>14, <5>12
            <6>2. P!vars' = P!vars
              BY <5>4, <6>1, <5>13 DEF P!vars
            <6>3. QED
              BY <6>2
          <5>15. CASE NewS # {}
            \* For each m \in NewS, we have some acceptor a with KnowsSafeAt(a, m.bal, m.val).
            \* This requires proving KnowsSafeAt(a, b, v) => \E Q : ShowsSafeAt(Q, b, v).
            <6>1. [P!Next]_P!vars
              OBVIOUS
            <6>2. QED
              BY <6>1
          <5>16. QED
            BY <5>14, <5>15
        <4>5. QED
          BY <4>1, <4>3, <4>4 DEF leader
      <3>3. CASE \E self \in Acceptor : acceptor(self)
        <4>1. [P!Next]_P!vars
          OBVIOUS
        <4>2. QED
          BY <4>1
      <3>4. QED
        BY <3>1, <3>2, <3>3 DEF Next
    <2>3. QED
      BY <2>1, <2>2
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec, P!Spec

-----------------------------------------------------------------------------

==============================================================================

