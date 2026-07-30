---- MODULE EWD840_proof_Round1 ----
EXTENDS EWD840_proof_Round1Scaffold
USE NAssumption
LEMMA Round1 ==
    TSpec => (terminated ~> (terminated /\ tpos = 0))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
