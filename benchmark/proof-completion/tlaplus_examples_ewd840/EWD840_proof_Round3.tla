---- MODULE EWD840_proof_Round3 ----
EXTENDS EWD840_proof_Round3Scaffold
USE NAssumption
LEMMA Round3 == TSpec => (terminated /\ tpos = 0 /\ allWhite
                            ~> terminated /\ tpos = 0 /\ allWhite /\ tcolor = "white")
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
