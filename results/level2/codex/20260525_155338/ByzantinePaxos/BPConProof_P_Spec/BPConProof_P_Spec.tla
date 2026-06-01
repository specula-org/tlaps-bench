
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

-----------------------------------------------------------------------------

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF
  <1>1. SUFFICES ASSUME NEW Q \in Quorum
                   PROVE Q # {}
    OBVIOUS
  <1>2. PICK S \in ByzQuorum : Q = S \cap Acceptor
    BY <1>1 DEF Quorum
  <1>3. S \cap S \cap Acceptor # {}
    BY <1>2, BQA DEF BQA
  <1>4. Q = S \cap S \cap Acceptor
    BY <1>2, SetExtensionality
  <1>5. Q # {}
    BY <1>3, <1>4
  <1> QED BY <1>5

-----------------------------------------------------------------------------

LEMMA InitImpliesPInit == Init => P!Init
PROOF BY QuorumNonEmpty, SetExtensionality
     DEF Init, P!Init, PmaxBal, MaxBallot, 1bOr2bMsgs,
         msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
         1bRestrict, P!None, None

-----------------------------------------------------------------------------

LEMMA MaxBallotEmpty == MaxBallot({}) = -1
PROOF BY DEF MaxBallot

LEMMA MaxBallotIsMax ==
  \A S \in SUBSET Int :
    IsFiniteSet(S) /\ S # {} =>
      /\ MaxBallot(S) \in S
      /\ \A x \in S : MaxBallot(S) >= x
PROOF
  <1>1. SUFFICES ASSUME NEW S \in SUBSET Int,
                          IsFiniteSet(S) /\ S # {}
                   PROVE /\ MaxBallot(S) \in S
                         /\ \A x \in S : MaxBallot(S) >= x
    OBVIOUS
  <1>2. \E max \in S : \A x \in S : max >= x
    BY <1>1, FiniteSetHasMax
  <1> QED BY <1>1, <1>2 DEF MaxBallot

LEMMA MaxBallotUpperBound ==
  \A S \in SUBSET Int :
    IsFiniteSet(S) /\ S # {} =>
      \A b \in Int :
        (\A x \in S : b >= x) => b >= MaxBallot(S)
PROOF
  <1>1. SUFFICES ASSUME NEW S \in SUBSET Int,
                          IsFiniteSet(S) /\ S # {},
                          NEW b \in Int,
                          \A x \in S : b >= x
                   PROVE b >= MaxBallot(S)
    OBVIOUS
  <1>2. MaxBallot(S) \in S
    BY <1>1, MaxBallotIsMax
  <1> QED BY <1>1, <1>2

LEMMA MaxBallotAddGeq ==
  \A S \in SUBSET Int :
    IsFiniteSet(S) =>
      \A b \in Int :
        b >= MaxBallot(S) => MaxBallot(S \cup {b}) = b
PROOF
  <1>1. SUFFICES ASSUME NEW S \in SUBSET Int,
                          IsFiniteSet(S),
                          NEW b \in Int,
                          b >= MaxBallot(S)
                   PROVE MaxBallot(S \cup {b}) = b
    OBVIOUS
  <1>2. S \cup {b} \in SUBSET Int
    BY <1>1
  <1>3. IsFiniteSet(S \cup {b})
    BY <1>1, SingletonSetFinite, UnionOfFiniteSetsFinite
  <1>4. b \in S \cup {b}
    OBVIOUS
  <1>5. CASE S = {}
    <2>1. S \cup {b} = {b}
      BY <1>5, SetExtensionality
    <2>2. MaxBallot(S \cup {b}) \in {b}
      BY <1>2, <1>3, <1>4, <2>1, MaxBallotIsMax
    <2>3. MaxBallot(S \cup {b}) = b
      BY <2>2
    <2> QED BY <2>3
  <1>6. CASE S # {}
    <2>1. \A x \in S : MaxBallot(S) >= x
      BY <1>1, <1>6, MaxBallotIsMax
    <2>2. \A x \in S \cup {b} : b >= x
    PROOF
      <3>1. SUFFICES ASSUME NEW x \in S \cup {b}
                       PROVE b >= x
        OBVIOUS
      <3>2. CASE x \in S
        <4>1. MaxBallot(S) >= x
          BY <2>1, <3>2
        <4>2. MaxBallot(S) \in Int
          BY <1>1, <1>6, MaxBallotIsMax
        <4>3. x \in Int
          BY <1>1, <3>2
        <4>4. b >= x
          BY <1>1, <4>1, <4>2, <4>3, SimpleArithmetic
        <4> QED BY <4>4
      <3>3. CASE x = b
        <4>1. b >= x
          BY <3>3, SimpleArithmetic
        <4> QED BY <4>1
      <3>4. x \in S \/ x = b
        BY <3>1
      <3> QED BY <3>2, <3>3, <3>4
    <2>3. MaxBallot(S \cup {b}) \in S \cup {b}
      BY <1>2, <1>3, <1>4, MaxBallotIsMax
    <2>4. MaxBallot(S \cup {b}) >= b
      BY <1>2, <1>3, <1>4, MaxBallotIsMax
    <2>5. b >= MaxBallot(S \cup {b})
      BY <2>2, <2>3
    <2>6. MaxBallot(S \cup {b}) \in Int
      BY <1>2, <2>3
    <2> QED BY <1>1, <2>4, <2>5, <2>6, SimpleArithmetic
  <1> QED BY <1>5, <1>6

-----------------------------------------------------------------------------

LEMMA MaxBallotAddUpper ==
  \A S \in SUBSET Int :
    \A b \in Int :
      (\A x \in S : b >= x) => MaxBallot(S \cup {b}) = b
PROOF
  <1>1. SUFFICES ASSUME NEW S \in SUBSET Int,
                          NEW b \in Int,
                          \A x \in S : b >= x
                   PROVE MaxBallot(S \cup {b}) = b
    OBVIOUS
  <1>2. S \cup {b} # {}
    OBVIOUS
  <1>3. b \in S \cup {b}
    OBVIOUS
  <1>4. \A x \in S \cup {b} : b >= x
  PROOF
    <2>1. SUFFICES ASSUME NEW x \in S \cup {b}
                     PROVE b >= x
      OBVIOUS
    <2>2. CASE x \in S
      <3>1. b >= x
        BY <1>1, <2>2
      <3> QED BY <3>1
    <2>3. CASE x = b
      <3>1. b >= x
        BY <2>3, SimpleArithmetic
      <3> QED BY <3>1
    <2>4. x \in S \/ x = b
      BY <2>1
    <2> QED BY <2>2, <2>3, <2>4
  <1>5. LET mb == CHOOSE y \in S \cup {b} :
                    \A x \in S \cup {b} : y >= x
          IN /\ mb \in S \cup {b}
             /\ \A x \in S \cup {b} : mb >= x
    BY <1>3, <1>4
  <1>6. MaxBallot(S \cup {b}) \in S \cup {b}
    BY <1>2, <1>5 DEF MaxBallot
  <1>7. \A x \in S \cup {b} : MaxBallot(S \cup {b}) >= x
    BY <1>2, <1>5 DEF MaxBallot
  <1>8. MaxBallot(S \cup {b}) >= b
    BY <1>3, <1>7
  <1>9. b >= MaxBallot(S \cup {b})
    BY <1>4, <1>6
  <1>10. MaxBallot(S \cup {b}) \in Int
    BY <1>1, <1>6
  <1> QED BY <1>1, <1>8, <1>9, <1>10, SimpleArithmetic

-----------------------------------------------------------------------------

BMsgsFor(a) == {ma \in 1bOr2bMsgs : ma.acc = a}

BalSet(a) == {m.bal : m \in BMsgsFor(a)}

BPTypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
            /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
            /\ maxVVal \in [Acceptor -> Value \cup {None}]
            /\ 2avSent \in [Acceptor -> SUBSET [val : Value, bal : Ballot]]
            /\ knowsSent \in [Acceptor -> SUBSET 1bMessage]

PMaxHistInv == \A m \in 1bOr2bMsgs :
                 /\ m.bal \in Ballot
                 /\ (m.acc \in Acceptor => maxBal[m.acc] >= m.bal)

PMaxBound == \A a \in Acceptor : PmaxBal[a] <= maxBal[a]

PMaxInv == BPTypeOK /\ PMaxHistInv /\ PMaxBound

LEMMA InitImpliesPMaxInv == Init => PMaxInv
PROOF BY EmptySetFinite
     DEF Init, PMaxInv, BPTypeOK, PMaxHistInv, PMaxBound, PmaxBal,
         MaxBallot, 1bOr2bMsgs, Ballot, None

LEMMA BalSetFinite ==
  IsFiniteSet(1bOr2bMsgs) => \A a \in Acceptor : IsFiniteSet(BalSet(a))
PROOF
  <1>1. SUFFICES ASSUME IsFiniteSet(1bOr2bMsgs),
                          NEW a \in Acceptor
                   PROVE IsFiniteSet(BalSet(a))
    OBVIOUS
  <1>2. BMsgsFor(a) \subseteq 1bOr2bMsgs
    BY DEF BMsgsFor
  <1>3. IsFiniteSet(BMsgsFor(a))
    BY <1>1, <1>2, SubsetOfFiniteSetFinite
  <1>4. LET f == [x \in BMsgsFor(a) |-> x.bal]
          IN IsFiniteSet({f[x] : x \in BMsgsFor(a)})
    BY <1>3, ImageOfFiniteSetFinite
  <1>5. LET f == [x \in BMsgsFor(a) |-> x.bal]
          IN {f[x] : x \in BMsgsFor(a)} = BalSet(a)
    BY SetExtensionality DEF BalSet
  <1> QED BY <1>4, <1>5

LEMMA BalSetSubsetInt ==
  PMaxHistInv => \A a \in Acceptor : BalSet(a) \in SUBSET Int
PROOF BY DEF BalSet, BMsgsFor, PMaxHistInv, Ballot

LEMMA PMaxLeMaxBal ==
  PMaxInv => \A a \in Acceptor : PmaxBal[a] <= maxBal[a]
PROOF BY DEF PMaxInv, PMaxBound

-----------------------------------------------------------------------------

BAcc1b(self, b) ==
  /\ b > maxBal[self]
  /\ sentMsgs("1a", b) # {}
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ bmsgs' = bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                            m2av |-> 2avSent[self],
                            mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>

BAcc2av(self, b) ==
  /\ maxBal[self] =< b
  /\ \A r \in 2avSent[self] : r.bal < b
  /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
       /\ bmsgs' = bmsgs \cup {[type |-> "2av", bal |-> b,
                                 val |-> m.val, acc |-> self]}
       /\ 2avSent' = [2avSent EXCEPT ![self] =
                         {r \in 2avSent[self] : r.val # m.val}
                         \cup {[val |-> m.val, bal |-> b]}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>

BAcc2b(self, b) ==
  /\ maxBal[self] =< b
  /\ \E v \in {vv \in Value :
                \E Q \in ByzQuorum :
                  \A aa \in Q :
                    \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                    /\ m.acc = aa}:
       /\ bmsgs' = bmsgs \cup {[type |-> "2b", acc |-> self,
                                 bal |-> b, val |-> v]}
       /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
  /\ UNCHANGED <<2avSent, knowsSent>>

BAccKnow(self, b) ==
  /\ \E S \in SUBSET sentMsgs("1b", b):
       knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
  /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

LEMMA AcceptorDef ==
  \A self \in Acceptor :
    acceptor(self) <=> \E b \in Ballot :
      \/ BAcc1b(self, b)
      \/ BAcc2av(self, b)
      \/ BAcc2b(self, b)
      \/ BAccKnow(self, b)
PROOF BY DEF acceptor, BAcc1b, BAcc2av, BAcc2b, BAccKnow

-----------------------------------------------------------------------------

BMessage == [type : {"1a"}, bal : Ballot]
            \cup [type : {"1c"}, bal : Ballot, val : Value]
            \cup 1bMessage \cup 2avMessage \cup 2bMessage

BMsgOK == bmsgs \subseteq BMessage

KnowInv == \A a \in Acceptor :
             knowsSent[a] \subseteq {m \in bmsgs : m.type = "1b"}

Real1bUnique ==
  \A m, n \in acceptorMsgsOfType("1b") :
    m.acc = n.acc /\ m.bal = n.bal => 1bRestrict(m) = 1bRestrict(n)

Real2avUnique ==
  \A m, n \in acceptorMsgsOfType("2av") :
    m.acc = n.acc /\ m.bal = n.bal => m.val = n.val

Real1bM2avSafe ==
  \A m \in acceptorMsgsOfType("1b") :
    \A r \in m.m2av :
      [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

TwoAvSentSafe ==
  \A a \in Acceptor :
    \A r \in 2avSent[a] :
      [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

TwoAvHistInv ==
  \A m \in acceptorMsgsOfType("2av") :
    \E r \in 2avSent[m.acc] : /\ r.val = m.val
                               /\ r.bal >= m.bal

IndInv == /\ PMaxInv
          /\ BMsgOK
          /\ KnowInv
          /\ Real1bUnique
          /\ Real2avUnique
          /\ Real1bM2avSafe
          /\ TwoAvSentSafe
          /\ TwoAvHistInv

LEMMA InitImpliesIndInv == Init => IndInv
PROOF BY InitImpliesPMaxInv, SetExtensionality
     DEF IndInv, Init, BMsgOK, BMessage, KnowInv, Real1bUnique,
         Real2avUnique, Real1bM2avSafe, TwoAvSentSafe, TwoAvHistInv,
         msgsOfType, acceptorMsgsOfType, msgs, 1bmsgs, 1cmsgs, 2amsgs

LEMMA AcceptorGrowsRaw ==
  \A self \in Acceptor :
    BPTypeOK /\ acceptor(self) => /\ bmsgs \subseteq bmsgs'
                                  /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
PROOF
  <1>1. SUFFICES ASSUME NEW self \in Acceptor,
                          BPTypeOK,
                          acceptor(self)
                   PROVE /\ bmsgs \subseteq bmsgs'
                         /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    OBVIOUS
  <1>2. PICK b \in Ballot :
            \/ BAcc1b(self, b)
            \/ BAcc2av(self, b)
            \/ BAcc2b(self, b)
            \/ BAccKnow(self, b)
    BY <1>1, AcceptorDef
  <1>3. CASE BAcc1b(self, b)
    <2>1. /\ bmsgs \subseteq bmsgs'
           /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
      BY <1>1, <1>3, SMTT(30), SetExtensionality
         DEF BPTypeOK, BAcc1b
    <2> QED BY <2>1
  <1>4. CASE BAcc2av(self, b)
    <2>1. /\ bmsgs \subseteq bmsgs'
           /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
      BY <1>1, <1>4, SMTT(30), SetExtensionality
         DEF BPTypeOK, BAcc2av
    <2> QED BY <2>1
  <1>5. CASE BAcc2b(self, b)
    <2>1. /\ bmsgs \subseteq bmsgs'
           /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
      BY <1>1, <1>5, SMTT(30), SetExtensionality
         DEF BPTypeOK, BAcc2b
    <2> QED BY <2>1
  <1>6. CASE BAccKnow(self, b)
    <2>1. /\ bmsgs \subseteq bmsgs'
           /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
      BY <1>1, <1>6, SMTT(30), SetExtensionality
         DEF BPTypeOK, BAccKnow, sentMsgs
    <2> QED BY <2>1
  <1> QED BY <1>2, <1>3, <1>4, <1>5, <1>6

LEMMA LeaderGrowsRaw ==
  \A self \in Ballot :
    BPTypeOK /\ leader(self) => /\ bmsgs \subseteq bmsgs'
                                /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
PROOF BY SMTT(30), SetExtensionality DEF BPTypeOK, leader

LEMMA FAcceptorGrowsRaw ==
  \A self \in FakeAcceptor :
    BPTypeOK /\ facceptor(self) => /\ bmsgs \subseteq bmsgs'
                                   /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
PROOF BY SMTT(30), SetExtensionality DEF BPTypeOK, facceptor

LEMMA StepGrowsRaw ==
  BPTypeOK /\ [Next]_vars => /\ bmsgs \subseteq bmsgs'
                             /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
PROOF
  <1>1. SUFFICES ASSUME BPTypeOK,
                          [Next]_vars
                   PROVE /\ bmsgs \subseteq bmsgs'
                         /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
    OBVIOUS
  <1>2. CASE Next
    <2>1. bmsgs \subseteq bmsgs'
      BY <1>1, <1>2, AcceptorGrowsRaw, LeaderGrowsRaw, FAcceptorGrowsRaw
         DEF Next
    <2>2. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
      BY <1>1, <1>2, AcceptorGrowsRaw, LeaderGrowsRaw, FAcceptorGrowsRaw
         DEF Next
    <2> QED BY <2>1, <2>2
  <1>3. CASE UNCHANGED vars
    <2>1. bmsgs' = bmsgs /\ knowsSent' = knowsSent
      BY <1>3 DEF vars
    <2>2. /\ bmsgs \subseteq bmsgs'
           /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
      BY <2>1
    <2> QED BY <2>2
  <1>4. Next \/ UNCHANGED vars
    BY <1>1 DEF vars
  <1> QED BY <1>2, <1>3, <1>4

LEMMA KnowsSafeAtMonotonic ==
  (\A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]) =>
    \A a \in Acceptor :
      \A b, v : KnowsSafeAt(a, b, v) => KnowsSafeAt(a, b, v)'
PROOF BY SMTT(30), SetExtensionality DEF KnowsSafeAt

LEMMA MsgsMonotonicFromRaw ==
  /\ bmsgs \subseteq bmsgs'
  /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
  => msgs \subseteq msgs'
PROOF
  <1>1. SUFFICES ASSUME /\ bmsgs \subseteq bmsgs'
                          /\ \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a],
                          NEW x \in msgs
                   PROVE x \in msgs'
    BY SetExtensionality
  <1>2. x \in msgsOfType("1a") \/ x \in 1bmsgs \/ x \in 1cmsgs \/
         x \in 2amsgs \/ x \in acceptorMsgsOfType("2b")
    BY <1>1 DEF msgs
  <1>3. CASE x \in msgsOfType("1a")
    <2>1. x \in msgs'
      BY <1>1, <1>3, SMTT(30)
         DEF msgs, msgsOfType
    <2> QED BY <2>1
  <1>4. CASE x \in 1bmsgs
    <2>1. PICK m \in acceptorMsgsOfType("1b") : x = 1bRestrict(m)
      BY <1>4 DEF 1bmsgs
    <2>2. m \in acceptorMsgsOfType("1b")'
      BY <1>1, <2>1, SMTT(30)
         DEF acceptorMsgsOfType, msgsOfType
    <2>3. x \in 1bmsgs'
      BY <2>1, <2>2 DEF 1bmsgs
    <2>4. x \in msgs'
      BY <2>3 DEF msgs
    <2> QED BY <2>4
  <1>5. CASE x \in 1cmsgs
    <2>1. x \in msgsOfType("1c")
      BY <1>5 DEF 1cmsgs
    <2>2. PICK a \in Acceptor : KnowsSafeAt(a, x.bal, x.val)
      BY <1>5 DEF 1cmsgs
    <2>3. KnowsSafeAt(a, x.bal, x.val)'
      BY <1>1, <2>2, KnowsSafeAtMonotonic
    <2>4. x \in msgsOfType("1c")'
      BY <1>1, <2>1, SMTT(30) DEF msgsOfType
    <2>5. x \in 1cmsgs'
      BY <2>2, <2>3, <2>4 DEF 1cmsgs
    <2>6. x \in msgs'
      BY <2>5 DEF msgs
    <2> QED BY <2>6
  <1>6. CASE x \in 2amsgs
    <2>1. PICK Q \in Quorum :
             \A a \in Q :
               \E m2av \in acceptorMsgsOfType("2av") :
                  /\ m2av.acc = a
                  /\ m2av.bal = x.bal
                  /\ m2av.val = x.val
      BY <1>6 DEF 2amsgs
    <2>2. \A a \in Q :
             \E m2av \in acceptorMsgsOfType("2av")' :
                /\ m2av.acc = a
                /\ m2av.bal = x.bal
                /\ m2av.val = x.val
      BY <1>1, <2>1, SMTT(30)
         DEF acceptorMsgsOfType, msgsOfType
    <2>3. x \in 2amsgs'
      BY <1>6, <2>1, <2>2 DEF 2amsgs
    <2>4. x \in msgs'
      BY <2>3 DEF msgs
    <2> QED BY <2>4
  <1>7. CASE x \in acceptorMsgsOfType("2b")
    <2>1. x \in acceptorMsgsOfType("2b")'
      BY <1>1, <1>7, SMTT(30)
         DEF acceptorMsgsOfType, msgsOfType
    <2>2. x \in msgs'
      BY <2>1 DEF msgs
    <2> QED BY <2>2
  <1> QED BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7

LEMMA MsgsMonotonic == BPTypeOK /\ [Next]_vars => msgs \subseteq msgs'
PROOF BY StepGrowsRaw, MsgsMonotonicFromRaw

LEMMA PMaxInvPreserved == IndInv /\ [Next]_vars => PMaxInv'
PROOF BY SMTT(30), BQA, AcceptorDef, PMaxLeMaxBal, MaxBallotAddUpper,
         EmptySetFinite, SingletonSetFinite, UnionOfFiniteSetsFinite,
         SubsetOfFiniteSetFinite, SetExtensionality
     DEF IndInv, PMaxInv, BPTypeOK, PMaxHistInv,
         Next, BAcc1b, BAcc2av, BAcc2b, BAccKnow, leader, facceptor, vars, sentMsgs,
         1bOr2bMsgs, Ballot, ByzAcceptor, BMessage,
         1bMessage, 2avMessage, 2bMessage

LEMMA BMsgOKPreserved == IndInv /\ [Next]_vars => BMsgOK'
PROOF BY SMTT(30), BQA, AcceptorDef, SetExtensionality
     DEF IndInv, BMsgOK, BMessage, PMaxInv, BPTypeOK,
         Next, BAcc1b, BAcc2av, BAcc2b, BAccKnow, leader, facceptor, vars, sentMsgs,
         Ballot, ByzAcceptor, 1bMessage, 2avMessage, 2bMessage

LEMMA KnowInvPreserved == IndInv /\ [Next]_vars => KnowInv'
PROOF BY SMTT(30), BQA, AcceptorDef, StepGrowsRaw, SetExtensionality
     DEF IndInv, KnowInv, BMsgOK, BMessage, PMaxInv, BPTypeOK,
         Next, BAcc1b, BAcc2av, BAcc2b, BAccKnow, leader, facceptor, vars, sentMsgs,
         Ballot, ByzAcceptor, 1bMessage, 2avMessage, 2bMessage

LEMMA Real1bUniquePreserved == IndInv /\ [Next]_vars => Real1bUnique'
PROOF BY SMTT(30), BQA, AcceptorDef, PMaxLeMaxBal, SetExtensionality
     DEF IndInv, Real1bUnique, PMaxInv, BPTypeOK, PMaxHistInv,
         Next, BAcc1b, BAcc2av, BAcc2b, BAccKnow, leader, facceptor, vars, sentMsgs,
         msgsOfType, acceptorMsgsOfType, 1bRestrict,
         1bOr2bMsgs, Ballot, ByzAcceptor, 1bMessage, 2avMessage, 2bMessage

LEMMA Real2avUniquePreserved == IndInv /\ [Next]_vars => Real2avUnique'
PROOF BY SMTT(30), BQA, AcceptorDef, SetExtensionality
     DEF IndInv, Real2avUnique, TwoAvHistInv, PMaxInv, BPTypeOK,
         Next, BAcc1b, BAcc2av, BAcc2b, BAccKnow, leader, facceptor, vars, sentMsgs,
         msgsOfType, acceptorMsgsOfType,
         Ballot, ByzAcceptor, 1bMessage, 2avMessage, 2bMessage

LEMMA Real1bM2avSafePreserved == IndInv /\ [Next]_vars => Real1bM2avSafe'
PROOF BY SMTT(30), BQA, AcceptorDef, MsgsMonotonic, SetExtensionality
     DEF IndInv, Real1bM2avSafe, TwoAvSentSafe, PMaxInv, BPTypeOK,
         Next, BAcc1b, BAcc2av, BAcc2b, BAccKnow, leader, facceptor, vars, sentMsgs,
         msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
         1bRestrict, Ballot, ByzAcceptor, 1bMessage, 2avMessage, 2bMessage

LEMMA TwoAvSentSafePreserved == IndInv /\ [Next]_vars => TwoAvSentSafe'
PROOF BY SMTT(30), BQA, AcceptorDef, MsgsMonotonic, SetExtensionality
     DEF IndInv, TwoAvSentSafe, PMaxInv, BPTypeOK,
         Next, BAcc1b, BAcc2av, BAcc2b, BAccKnow, leader, facceptor, vars, sentMsgs,
         msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
         1bRestrict, Ballot, ByzAcceptor, 1bMessage, 2avMessage, 2bMessage

LEMMA TwoAvHistInvPreserved == IndInv /\ [Next]_vars => TwoAvHistInv'
PROOF BY SMTT(30), BQA, AcceptorDef, SetExtensionality
     DEF IndInv, TwoAvHistInv, PMaxInv, BPTypeOK,
         Next, BAcc1b, BAcc2av, BAcc2b, BAccKnow, leader, facceptor, vars, sentMsgs,
         msgsOfType, acceptorMsgsOfType,
         Ballot, ByzAcceptor, 1bMessage, 2avMessage, 2bMessage

LEMMA IndInvInductive == IndInv /\ [Next]_vars => IndInv'
PROOF BY PMaxInvPreserved, BMsgOKPreserved, KnowInvPreserved,
         Real1bUniquePreserved, Real2avUniquePreserved,
         Real1bM2avSafePreserved, TwoAvSentSafePreserved,
         TwoAvHistInvPreserved
     DEF IndInv

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

THEOREM Spec => P!Spec
PROOF OBVIOUS

-----------------------------------------------------------------------------

==============================================================================
