
---------------------------- MODULE BPConProof_P_Spec ------------------------------

EXTENDS BPConProof

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

1bOr2bMsgs == {m \in bmsgs : m.type \in {"1b", "2b"}}

PmaxBal == [a \in Acceptor |-> 
              MaxBallot({m.bal : m \in {ma \in 1bOr2bMsgs : 
                                           ma.acc = a}})]

P == INSTANCE PConProof WITH maxBal <- PmaxBal

THEOREM Spec => P!Spec
PROOF OBVIOUS

==============================================================================

