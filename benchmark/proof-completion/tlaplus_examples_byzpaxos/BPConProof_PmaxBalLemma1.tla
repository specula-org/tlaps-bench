---- MODULE BPConProof_PmaxBalLemma1 ----
EXTENDS BPConProof_PmaxBalLemma1Scaffold
LEMMA PmaxBalLemma1 ==
         ASSUME NEW m ,
                bmsgs' = bmsgs \cup {m},
                m.type # "1b" /\ m.type # "2b"
         PROVE  PmaxBal' = PmaxBal
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
