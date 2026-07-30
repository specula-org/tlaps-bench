---- MODULE ReadersWriters_proof_SafetyStep ----
EXTENDS ReadersWriters_proof_SafetyStepScaffold
LEMMA SafetyStep == Inv /\ [Next]_vars => Inv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
