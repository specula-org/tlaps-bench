---- MODULE TCommit_proof_TCorrect ----
EXTENDS TCommit_proof_TCorrectDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM TCorrect == TCSpec => []Inv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
