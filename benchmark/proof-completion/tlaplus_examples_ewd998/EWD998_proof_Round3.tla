---- MODULE EWD998_proof_Round3 ----
EXTENDS EWD998_proof_Round3Scaffold
USE NAssumption
LEMMA Round3 == BSpec => (Termination /\ atMaster /\ allWhite
                            ~> Termination /\ atMaster /\ allWhite /\ tknWhite /\ tknCount)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
