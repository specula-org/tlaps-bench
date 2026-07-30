---- MODULE BPConProof_PmaxBalLemma2 ----
EXTENDS BPConProof_PmaxBalLemma2Scaffold
LEMMA PmaxBalLemma2 ==
        ASSUME NEW m,
               bmsgs' = bmsgs \cup {m},
               NEW a \in Acceptor,
               m.acc # a
        PROVE  PmaxBal'[a] = PmaxBal[a]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
