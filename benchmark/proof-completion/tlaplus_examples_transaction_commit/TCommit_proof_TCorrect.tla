---- MODULE TCommit_proof_TCorrect ----
EXTENDS TCommit_proof_TCorrectScaffold
THEOREM TCorrect == TCSpec => []Inv
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
