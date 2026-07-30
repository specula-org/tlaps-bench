---- MODULE TwoPhase_proof_Consistency ----
EXTENDS TwoPhase_proof_ConsistencyScaffold
THEOREM Consistency == TPSpec => []TC!TCConsistent
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
