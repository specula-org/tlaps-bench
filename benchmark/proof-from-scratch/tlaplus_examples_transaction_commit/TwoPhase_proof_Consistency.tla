---- MODULE TwoPhase_proof_Consistency ----
EXTENDS TwoPhase_proof_ConsistencyDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Consistency == TPSpec => []TC!TCConsistent
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
