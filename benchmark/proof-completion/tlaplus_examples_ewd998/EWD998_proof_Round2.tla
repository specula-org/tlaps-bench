---- MODULE EWD998_proof_Round2 ----
EXTENDS EWD998_proof_Round2Scaffold
USE NAssumption
LEMMA Round2 == BSpec => (Termination /\ atMaster
                            ~> Termination /\ atMaster /\ allWhite)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
