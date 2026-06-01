
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

New1bMsg(self, b) ==
  [type  |-> "1b", bal |-> b,
   mbal |-> maxVBal[self], mval |-> maxVVal[self],
   m2av |-> 2avSent[self], acc |-> self]

Do1b(self, b) ==
  /\ b > maxBal[self]
  /\ sentMsgs("1a", b) # {}
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ bmsgs' = bmsgs \cup {New1bMsg(self, b)}
  /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>

Do2av(self, b, m) ==
  /\ maxBal[self] =< b
  /\ \A r \in 2avSent[self] : r.bal < b
  /\ m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}
  /\ bmsgs' = bmsgs \cup {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]}
  /\ 2avSent' = [2avSent EXCEPT ![self] = {r \in 2avSent[self] : r.val # m.val}
                                            \cup {[val |-> m.val, bal |-> b]}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>

Do2b(self, b, v) ==
  /\ maxBal[self] =< b
  /\ v \in {vv \in Value :
              \E Q \in ByzQuorum :
                \A aa \in Q :
                  \E m \in sentMsgs("2av", b) :
                    /\ m.val = vv
                    /\ m.acc = aa}
  /\ bmsgs' = bmsgs \cup {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
  /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
  /\ UNCHANGED <<2avSent, knowsSent>>

DoLearn1b(self, b, S) ==
  /\ S \in SUBSET sentMsgs("1b", b)
  /\ knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
  /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

DoLeader1a(self) ==
  /\ bmsgs' = bmsgs \cup {[type |-> "1a", bal |-> self]}
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

DoLeader1c(self, S) ==
  /\ S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]
  /\ bmsgs' = bmsgs \cup S
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

DoFake(self, m) ==
  /\ m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
             mm.acc = self}
  /\ bmsgs' = bmsgs \cup {m}
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

LEMMA InitInv == Init => Inv
PROOF
<1>1. Init => TypeOK
  BY Z3T(20) DEF Init, TypeOK, BMessage, 1aMessage, 1bMessage,
     1cMessage, 2avMessage, 2bMessage, ByzAcceptor, Ballot, None
<1>2. Init => 1bOr2bMsgs = {}
  BY IsaWithSetExtensionality DEF Init, 1bOr2bMsgs
<1>3. Init => bmsgsFinite
  BY <1>2, EmptySetFinite DEF bmsgsFinite
<1>4. Init => 1bInv1
  BY Z3T(20) DEF Init, 1bInv1
<1>5. Init => 1bInv2
  BY Z3T(20) DEF Init, 1bInv2
<1>6. Init => maxBalInv
  BY Z3T(20) DEF Init, maxBalInv
<1>7. Init => 2avInv1
  BY Z3T(20) DEF Init, 2avInv1
<1>8. Init => 2avInv2
  BY Z3T(20) DEF Init, 2avInv2
<1>9. Init => 2avInv3
  BY Z3T(20) DEF Init, 2avInv3
<1>10. Init => accInv
  BY Z3T(20) DEF Init, accInv
<1>11. Init => knowsSentInv
  BY Z3T(20) DEF Init, knowsSentInv, msgsOfType
<1> QED
  BY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11
  DEF Inv

LEMMA VarsUnchanged ==
  UNCHANGED vars =>
    /\ maxBal' = maxBal
    /\ maxVBal' = maxVBal
    /\ maxVVal' = maxVVal
    /\ 2avSent' = 2avSent
    /\ knowsSent' = knowsSent
    /\ bmsgs' = bmsgs
PROOF
  BY Z3T(20) DEF vars

LEMMA AddBmsgFinite ==
  \A x : bmsgsFinite => IsFiniteSet({m \in bmsgs \cup {x} : m.type \in {"1b", "2b"}})
PROOF
<1>1. \A x : {m \in bmsgs \cup {x} : m.type \in {"1b", "2b"}}
             \subseteq 1bOr2bMsgs \cup {x}
  BY Z3T(20) DEF 1bOr2bMsgs
<1>2. \A x : bmsgsFinite => IsFiniteSet(1bOr2bMsgs \cup {x})
  BY SingletonSetFinite, UnionOfFiniteSetsFinite DEF bmsgsFinite
<1> QED
  BY <1>1, <1>2, SubsetOfFiniteSetFinite

LEMMA AddNon1b2bFinite ==
  \A S :
    /\ bmsgsFinite
    /\ \A x \in S : x.type \notin {"1b", "2b"}
    => IsFiniteSet({m \in bmsgs \cup S : m.type \in {"1b", "2b"}})
PROOF
<1>1. \A S :
        (\A x \in S : x.type \notin {"1b", "2b"}) =>
        {m \in bmsgs \cup S : m.type \in {"1b", "2b"}} \subseteq 1bOr2bMsgs
  BY Z3T(20) DEF 1bOr2bMsgs
<1> QED
  BY <1>1, SubsetOfFiniteSetFinite DEF bmsgsFinite

LEMMA KnowsSafeAtMono ==
  \A ac, b, v :
    knowsSent[ac] \subseteq knowsSent'[ac] =>
      (KnowsSafeAt(ac, b, v) => KnowsSafeAt(ac, b, v)')
PROOF
  BY Z3T(20) DEF KnowsSafeAt

LEMMA MsgsOfTypeMono ==
  \A t : bmsgs \subseteq bmsgs' => msgsOfType(t) \subseteq msgsOfType(t)'
PROOF
  BY Z3T(20) DEF msgsOfType

LEMMA AcceptorMsgsOfTypeMono ==
  \A t : bmsgs \subseteq bmsgs' => acceptorMsgsOfType(t) \subseteq acceptorMsgsOfType(t)'
PROOF
  BY MsgsOfTypeMono, Z3T(20) DEF acceptorMsgsOfType

LEMMA OneBMsgsMono ==
  bmsgs \subseteq bmsgs' => 1bmsgs \subseteq 1bmsgs'
PROOF
  BY AcceptorMsgsOfTypeMono, Z3T(20) DEF 1bmsgs, 1bRestrict

LEMMA OneCMsgsMono ==
  /\ bmsgs \subseteq bmsgs'
  /\ \A ac \in Acceptor : knowsSent[ac] \subseteq knowsSent'[ac]
  => 1cmsgs \subseteq 1cmsgs'
PROOF
  BY MsgsOfTypeMono, KnowsSafeAtMono, Z3T(20) DEF 1cmsgs

LEMMA TwoAMsgsMono ==
  bmsgs \subseteq bmsgs' => 2amsgs \subseteq 2amsgs'
PROOF
  BY AcceptorMsgsOfTypeMono, Z3T(20) DEF 2amsgs, Quorum

LEMMA MsgsMono ==
  /\ bmsgs \subseteq bmsgs'
  /\ \A ac \in Acceptor : knowsSent[ac] \subseteq knowsSent'[ac]
  => msgs \subseteq msgs'
PROOF
  BY MsgsOfTypeMono, AcceptorMsgsOfTypeMono, OneBMsgsMono, OneCMsgsMono,
     TwoAMsgsMono, Z3T(20) DEF msgs

LEMMA Do1bFacts ==
  ASSUME NEW self \in Acceptor, NEW b \in Ballot
  PROVE Do1b(self, b) =>
    /\ bmsgs \subseteq bmsgs'
    /\ \A ac \in Acceptor : knowsSent[ac] \subseteq knowsSent'[ac]
    /\ maxVBal' = maxVBal
    /\ maxVVal' = maxVVal
    /\ 2avSent' = 2avSent
    /\ knowsSent' = knowsSent
PROOF
  BY Z3T(20) DEF Do1b, New1bMsg

LEMMA RecTest == \A b \in Ballot : [type |-> "1a", bal |-> b] \in 1aMessage
PROOF
  BY Z3T(20) DEF 1aMessage

LEMMA Rec1bTest ==
  \A b \in Ballot :
  \A mb \in Ballot \cup {-1} :
  \A mv \in Value \cup {None} :
  \A S \in SUBSET [val : Value, bal : Ballot] :
  \A a \in ByzAcceptor :
    [type |-> "1b", bal |-> b, mbal |-> mb, mval |-> mv,
     m2av |-> S, acc |-> a] \in 1bMessage
PROOF
  BY Zenon DEF 1bMessage

LEMMA IntGtLeContradiction ==
  \A x, y \in Int : y > x /\ y =< x => FALSE
PROOF
  BY SimpleArithmetic

LEMMA ExceptSameInDomain ==
  \A S, T : \A f \in [S -> T] : \A x \in S : \A y :
    [f EXCEPT ![x] = y][x] = y
PROOF
  BY Z3T(20)

LEMMA ExceptOtherInDomain ==
  \A S, T : \A f \in [S -> T] : \A x \in S : \A y : \A z \in S :
    z # x => [f EXCEPT ![x] = y][z] = f[z]
PROOF
  BY Z3T(20)

LEMMA New1bMsgType ==
  \A self, b :
    (/\ b \in Ballot
     /\ maxVBal[self] \in Ballot \cup {-1}
     /\ maxVVal[self] \in Value \cup {None}
     /\ 2avSent[self] \in SUBSET [val : Value, bal : Ballot]
     /\ self \in ByzAcceptor)
    => New1bMsg(self, b) \in 1bMessage
PROOF
  BY Rec1bTest, Z3T(20) DEF New1bMsg

LEMMA Do1bMaxBalMono ==
  \A self \in Acceptor : \A b \in Ballot :
        Inv /\ Do1b(self, b) =>
          \A a \in Acceptor : maxBal'[a] >= maxBal[a]
PROOF
<1>1. \A self \in Acceptor : \A b \in Ballot : \A a \in Acceptor :
        (/\ Inv
         /\ Do1b(self, b)
         /\ a = self)
        => maxBal'[a] >= maxBal[a]
  BY ExceptSameInDomain, SimpleArithmetic, Z3T(20) DEF Inv, TypeOK, Do1b, New1bMsg
<1>2. \A self \in Acceptor : \A b \in Ballot : \A a \in Acceptor :
        (/\ Inv
         /\ Do1b(self, b)
         /\ a # self)
        => maxBal'[a] = maxBal[a]
  BY ExceptOtherInDomain, Z3T(20) DEF Inv, TypeOK, Do1b, New1bMsg
<1>3. \A self \in Acceptor : \A b \in Ballot : \A a \in Acceptor :
        (/\ Inv
         /\ Do1b(self, b)
         /\ a # self)
        => maxBal'[a] >= maxBal[a]
  BY <1>2, SimpleArithmetic, Z3T(20) DEF Inv, TypeOK, Ballot
<1> QED
  BY <1>1, <1>3, Z3T(20)

LEMMA Do1bNoOldSame ==
  \A self \in Acceptor : \A b \in Ballot :
        Inv /\ Do1b(self, b) =>
          \A m \in bmsgs :
            (/\ m.type = "1b"
             /\ m.acc = self
             /\ m.bal = b)
            => FALSE
PROOF
  BY IntGtLeContradiction, SimpleArithmetic, Z3T(20)
  DEF Inv, TypeOK, maxBalInv, Do1b, New1bMsg, Ballot

LEMMA InvDo1b ==
  ASSUME NEW self \in Acceptor, NEW b \in Ballot
  PROVE  Inv /\ Do1b(self, b) => Inv'
PROOF
<1>1. Inv /\ Do1b(self, b) => TypeOK'
  PROOF
  <2>1. Inv /\ Do1b(self, b) => maxBal' \in [Acceptor -> Ballot \cup {-1}]
    BY Z3T(20) DEF Inv, TypeOK, Do1b, New1bMsg
  <2>2. Inv /\ Do1b(self, b) => 2avSent' \in [Acceptor -> SUBSET [val : Value, bal : Ballot]]
    BY Do1bFacts, Z3T(20) DEF Inv, TypeOK
  <2>3. Inv /\ Do1b(self, b) => maxVBal' \in [Acceptor -> Ballot \cup {-1}]
    BY Do1bFacts, Z3T(20) DEF Inv, TypeOK
  <2>4. Inv /\ Do1b(self, b) => maxVVal' \in [Acceptor -> Value \cup {None}]
    BY Do1bFacts, Z3T(20) DEF Inv, TypeOK, None
  <2>5. Inv /\ Do1b(self, b) => knowsSent' \in [Acceptor -> SUBSET 1bMessage]
    BY Do1bFacts, Z3T(20) DEF Inv, TypeOK, 1bMessage, ByzAcceptor
  <2>6. Inv => maxVBal[self] \in Ballot \cup {-1}
    BY Z3T(20) DEF Inv, TypeOK
  <2>7. Inv => maxVVal[self] \in Value \cup {None}
    BY Z3T(20) DEF Inv, TypeOK
  <2>8. Inv => 2avSent[self] \in SUBSET [val : Value, bal : Ballot]
    BY Z3T(20) DEF Inv, TypeOK
  <2>9. self \in ByzAcceptor
    BY Z3T(20) DEF ByzAcceptor
  <2>10. Inv /\ Do1b(self, b) =>
          New1bMsg(self, b) \in 1bMessage
    BY <2>6, <2>7, <2>8, <2>9, New1bMsgType, Z3T(20)
    DEF Inv, TypeOK, New1bMsg, 1bMessage, ByzAcceptor, Ballot, None
  <2>11. Inv /\ Do1b(self, b) => bmsgs' \subseteq BMessage
    BY <2>10, BQA, Z3T(20)
    DEF Inv, TypeOK, Do1b, New1bMsg, BMessage, 1aMessage, 1bMessage, 1cMessage,
        2avMessage, 2bMessage, ByzAcceptor, Ballot, None
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>11 DEF TypeOK
<1>2. Inv /\ Do1b(self, b) => bmsgsFinite'
  BY AddBmsgFinite, Z3T(20) DEF Inv, bmsgsFinite, 1bOr2bMsgs, Do1b, New1bMsg
<1>3. Inv /\ Do1b(self, b) => 1bInv1'
  BY Do1bFacts, MsgsMono, Z3T(20) DEF Inv, 1bInv1, accInv, Do1b, New1bMsg
<1>4. Inv /\ Do1b(self, b) => 1bInv2'
  BY Do1bNoOldSame, SimpleArithmetic, Z3T(20)
  DEF Inv, 1bInv2, maxBalInv, Do1b, New1bMsg
<1>5. Inv /\ Do1b(self, b) => maxBalInv'
  BY Do1bMaxBalMono, SimpleArithmetic, Z3T(20) DEF Inv, maxBalInv, Do1b, New1bMsg
<1>6. Inv /\ Do1b(self, b) => 2avInv1'
  BY Z3T(20) DEF Inv, 2avInv1, Do1b, New1bMsg
<1>7. Inv /\ Do1b(self, b) => 2avInv2'
  BY Do1bFacts, MsgsMono, Z3T(20) DEF Inv, 2avInv2, Do1b, New1bMsg
<1>8. Inv /\ Do1b(self, b) => 2avInv3'
  BY Do1bFacts, MsgsMono, Z3T(20) DEF Inv, 2avInv3, Do1b, New1bMsg
<1>9. Inv /\ Do1b(self, b) => accInv'
  BY Do1bFacts, Do1bMaxBalMono, MsgsMono, SimpleArithmetic, Z3T(20)
  DEF Inv, accInv, Do1b, New1bMsg
<1>10. Inv /\ Do1b(self, b) => knowsSentInv'
  BY Do1bFacts, MsgsOfTypeMono, Z3T(20) DEF Inv, knowsSentInv, Do1b, New1bMsg
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10
  DEF Inv

LEMMA InvDo2av ==
  \A self \in Acceptor : \A b \in Ballot : \A m : Inv /\ Do2av(self, b, m) => Inv'
PROOF
  BY EmptySetFinite, SingletonSetFinite, ImageOfFiniteSetFinite,
     SubsetOfFiniteSetFinite, UnionOfFiniteSetsFinite, BQA,
     AddBmsgFinite, MsgsMono, Force
  DEF Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
      maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv,
      Do2av, sentMsgs, KnowsSafeAt,
      msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
      1bRestrict, Quorum, BMessage, 1aMessage, 1bMessage, 1cMessage,
      2avMessage, 2bMessage, ByzAcceptor, Ballot, None

LEMMA InvDo2b ==
  \A self \in Acceptor : \A b \in Ballot : \A v : Inv /\ Do2b(self, b, v) => Inv'
PROOF
  BY EmptySetFinite, SingletonSetFinite, ImageOfFiniteSetFinite,
     SubsetOfFiniteSetFinite, UnionOfFiniteSetsFinite, BQA,
     AddBmsgFinite, MsgsMono, Force
  DEF Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
      maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv,
      Do2b, sentMsgs, KnowsSafeAt,
      msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
      1bRestrict, Quorum, BMessage, 1aMessage, 1bMessage, 1cMessage,
      2avMessage, 2bMessage, ByzAcceptor, Ballot, None

LEMMA InvDoLearn1b ==
  \A self \in Acceptor : \A b \in Ballot : \A S : Inv /\ DoLearn1b(self, b, S) => Inv'
PROOF
  BY EmptySetFinite, SingletonSetFinite, ImageOfFiniteSetFinite,
     SubsetOfFiniteSetFinite, UnionOfFiniteSetsFinite, BQA,
     MsgsMono, Force
  DEF Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
      maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv,
      DoLearn1b, sentMsgs, KnowsSafeAt,
      msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
      1bRestrict, Quorum, BMessage, 1aMessage, 1bMessage, 1cMessage,
      2avMessage, 2bMessage, ByzAcceptor, Ballot, None

LEMMA InvDoLeader1a ==
  \A self \in Ballot : Inv /\ DoLeader1a(self) => Inv'
PROOF
  BY EmptySetFinite, SingletonSetFinite, ImageOfFiniteSetFinite,
     SubsetOfFiniteSetFinite, UnionOfFiniteSetsFinite, BQA,
     AddBmsgFinite, MsgsMono, Force
  DEF Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
      maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv,
      DoLeader1a, sentMsgs, KnowsSafeAt,
      msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
      1bRestrict, Quorum, BMessage, 1aMessage, 1bMessage, 1cMessage,
      2avMessage, 2bMessage, ByzAcceptor, Ballot, None

LEMMA InvDoLeader1c ==
  \A self \in Ballot : \A S : Inv /\ DoLeader1c(self, S) => Inv'
PROOF
  BY EmptySetFinite, SingletonSetFinite, ImageOfFiniteSetFinite,
     SubsetOfFiniteSetFinite, UnionOfFiniteSetsFinite, BQA,
     AddNon1b2bFinite, MsgsMono, Force
  DEF Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
      maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv,
      DoLeader1c, sentMsgs, KnowsSafeAt,
      msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
      1bRestrict, Quorum, BMessage, 1aMessage, 1bMessage, 1cMessage,
      2avMessage, 2bMessage, ByzAcceptor, Ballot, None

LEMMA InvDoFake ==
  \A self \in FakeAcceptor : \A m : Inv /\ DoFake(self, m) => Inv'
PROOF
  BY EmptySetFinite, SingletonSetFinite, ImageOfFiniteSetFinite,
     SubsetOfFiniteSetFinite, UnionOfFiniteSetsFinite, BQA,
     AddBmsgFinite, MsgsMono, Force
  DEF Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
      maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv,
      DoFake, sentMsgs, KnowsSafeAt,
      msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
      1bRestrict, Quorum, BMessage, 1aMessage, 1bMessage, 1cMessage,
      2avMessage, 2bMessage, ByzAcceptor, Ballot, None

LEMMA InvAcceptor ==
  \A self \in Acceptor : Inv /\ acceptor(self) => Inv'
PROOF
  BY InvDo1b, InvDo2av, InvDo2b, InvDoLearn1b, Force
  DEF acceptor, Do1b, New1bMsg, Do2av, Do2b, DoLearn1b

LEMMA InvLeader ==
  \A self \in Ballot : Inv /\ leader(self) => Inv'
PROOF
  BY InvDoLeader1a, InvDoLeader1c, Force
  DEF leader, DoLeader1a, DoLeader1c

LEMMA InvFake ==
  \A self \in FakeAcceptor : Inv /\ facceptor(self) => Inv'
PROOF
  BY InvDoFake, Force
  DEF facceptor, DoFake

LEMMA InvNext == Inv /\ [Next]_vars => Inv'
PROOF
<1>1. Inv /\ Next => Inv'
  BY InvAcceptor, InvLeader, InvFake DEF Next
<1>2. Inv /\ UNCHANGED vars => Inv'
  BY VarsUnchanged, Force
  DEF Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
      maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv,
      msgs, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs,
      1bRestrict, Quorum, sentMsgs, KnowsSafeAt, vars
<1> QED
  BY <1>1, <1>2 DEF vars

THEOREM Spec => []Inv    
PROOF
  BY InitInv, InvNext, PTL DEF Spec
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

==============================================================================
