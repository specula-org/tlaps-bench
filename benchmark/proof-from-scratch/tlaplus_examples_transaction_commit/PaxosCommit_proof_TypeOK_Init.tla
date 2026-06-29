------------------------- MODULE PaxosCommit_proof_TypeOK_Init -------------------------

EXTENDS PaxosCommit, FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

THEOREM TypeOK_Init == PCSpec => PCTypeOK
PROOF OBVIOUS

============================================================================
