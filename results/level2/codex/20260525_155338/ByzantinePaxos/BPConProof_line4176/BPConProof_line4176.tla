
---------------------------- MODULE BPConProof_line4176 ------------------------------

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

-----------------------------------------------------------------------------

VARIABLES maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs

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

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

chosen == {v \in Value : \E BQ \in ByzQuorum, b \in Ballot :
                           \A a \in BQ : \E m \in msgs : /\ m.type = "2b"
                                                         /\ m.acc  = a
                                                         /\ m.bal  = b
                                                         /\ m.val  = v}

THEOREM chosen \subseteq P!chosen

PROOF
  <1>1. SUFFICES ASSUME NEW v \in chosen
                  PROVE  v \in P!chosen
    OBVIOUS
  <1>2. v \in Value
    BY <1>1 DEF chosen
  <1>3. PICK BQ \in ByzQuorum, b \in Ballot :
            \A a \in BQ : \E m \in msgs : /\ m.type = "2b"
                                             /\ m.acc  = a
                                             /\ m.bal  = b
                                             /\ m.val  = v
    BY <1>1 DEF chosen
  <1>4. BQ \cap Acceptor \in Quorum
    BY <1>3 DEF Quorum
  <1>5. \A a \in BQ \cap Acceptor :
            \E m \in msgs : /\ m.type = "2b"
                             /\ m.acc  = a
                             /\ m.bal  = b
                             /\ m.val  = v
    BY <1>3
  <1>6. b \in P!Ballot
    BY <1>3 DEF P!Ballot, Ballot
  <1>7. \E Q \in Quorum, bb \in P!Ballot :
            \A a \in Q : \E m \in msgs : /\ m.type = "2b"
                                           /\ m.acc  = a
                                           /\ m.bal  = bb
                                           /\ m.val  = v
    BY <1>4, <1>5, <1>6
  <1>8. QED
    BY <1>2, <1>7 DEF P!chosen

==============================================================================
