---- MODULE ReadersWriters_proof_SafetyCorrect ----
EXTENDS ReadersWriters_proof_SafetyCorrectScaffold
THEOREM SafetyCorrect == Spec => []Safety
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
