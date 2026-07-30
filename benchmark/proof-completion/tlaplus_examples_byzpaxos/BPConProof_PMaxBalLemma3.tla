---- MODULE BPConProof_PMaxBalLemma3 ----
EXTENDS BPConProof_PMaxBalLemma3Scaffold
LEMMA PMaxBalLemma3 ==
        ASSUME TypeOK,
               bmsgsFinite,
               NEW a \in Acceptor
        PROVE  LET S == {m.bal : m \in {ma \in bmsgs :
                                           /\ ma.type \in {"1b", "2b"}
                                           /\ ma.acc = a}}
               IN  /\ IsFiniteSet(S)
                   /\ S \in SUBSET Ballot
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
