---- MODULE BPConProof_MsgsLemma ----
EXTENDS BPConProof_MsgsLemmaScaffold
LEMMA MsgsLemma ==
TypeOK =>
    /\ \A self \in Acceptor, b \in Ballot :
         Phase1b(self, b) =>
            msgs' = msgs \cup
                     {[type |-> "1b", acc |-> self, bal |-> b,
                       mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
    /\ \A self \in Acceptor, b \in Ballot :
         Phase2av(self, b) =>
            \/ msgs' = msgs
            \/ \E v \in Value :
                 /\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
                 /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
    /\ \A self \in Acceptor, b \in Ballot :
          Phase2b(self, b) =>
             \E v \in Value :
               /\ \E Q \in ByzQuorum :
                    \A a \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = v
                                                     /\ m.acc = a
               /\ msgs' = msgs \cup
                            {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
               /\ bmsgs' = bmsgs \cup
                            {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
               /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
    /\ \A self \in Acceptor, b \in Ballot :
          LearnsSent(self, b) =>
            \E S \in SUBSET {m \in msgsOfType("1c") : m.bal = b} :
                     msgs' = msgs \cup S
    /\ \A self \in Ballot :
         Phase1a(self) =>
           msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
    /\ \A self \in Ballot :
         Phase1c(self) =>
           \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
              /\ \A m \in S :
                    \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
              /\ msgs' = msgs \cup S
    /\ \A self \in FakeAcceptor : FakingAcceptor(self) => msgs' = msgs
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
