---- MODULE EWD998_proof_Round1 ----
EXTENDS EWD998_proof_Round1Scaffold
USE NAssumption
LEMMA Round1 == BSpec => (Termination
                            ~> Termination /\ atMaster)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
