--------------------------- MODULE TwoPhase_proof_Consistency --------------------------

EXTENDS TwoPhase, TLAPS

THEOREM Consistency == TPSpec => []TC!TCConsistent
PROOF OBVIOUS

============================================================================
