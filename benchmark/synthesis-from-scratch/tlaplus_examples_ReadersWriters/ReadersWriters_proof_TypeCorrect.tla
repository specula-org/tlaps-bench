--------------------- MODULE ReadersWriters_proof_TypeCorrect ----------------------------

EXTENDS ReadersWriters, FiniteSets, FiniteSetTheorems, TLAPS

ASSUME NumActorsIsNat == NumActors \in Nat

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

============================================================================
