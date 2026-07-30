---- MODULE BPConProof_PmaxBalLemma4 ----
EXTENDS BPConProof_PmaxBalLemma4Scaffold
LEMMA PmaxBalLemma4 ==
        ASSUME TypeOK,
               maxBalInv,
               bmsgsFinite,
               NEW a \in Acceptor
        PROVE  PmaxBal[a] =< maxBal[a]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
