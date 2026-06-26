--------------------------- MODULE TCommit_proof_TCorrect ---------------------------

EXTENDS TCommit, TLAPS

Inv == TCTypeOK /\ TCConsistent

THEOREM TCorrect == TCSpec => []Inv
PROOF OBVIOUS

============================================================================
