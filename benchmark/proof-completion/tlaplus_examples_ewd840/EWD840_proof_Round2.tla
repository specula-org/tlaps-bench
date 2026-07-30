---- MODULE EWD840_proof_Round2 ----
EXTENDS EWD840_proof_Round2Scaffold
USE NAssumption
LEMMA Round2 == TSpec => (terminated /\ tpos = 0
                            ~> terminated /\ tpos = 0 /\ allWhite)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
