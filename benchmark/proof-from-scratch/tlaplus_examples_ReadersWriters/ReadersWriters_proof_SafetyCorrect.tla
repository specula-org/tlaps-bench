---- MODULE ReadersWriters_proof_SafetyCorrect ----
EXTENDS ReadersWriters_proof_SafetyCorrectDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM SafetyCorrect == Spec => []Safety
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
