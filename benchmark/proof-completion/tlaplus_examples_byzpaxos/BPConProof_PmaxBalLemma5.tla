---- MODULE BPConProof_PmaxBalLemma5 ----
EXTENDS BPConProof_PmaxBalLemma5Scaffold
LEMMA PmaxBalLemma5 ==
        ASSUME TypeOK, bmsgsFinite, NEW a \in Acceptor
        PROVE  PmaxBal[a] \in Ballot \cup {-1}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
