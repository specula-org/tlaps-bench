--------------------- MODULE ReadersWriters_proof_SafetyCorrect ----------------------------

EXTENDS ReadersWriters, FiniteSets, FiniteSetTheorems, TLAPS

ASSUME NumActorsIsNat == NumActors \in Nat

THEOREM SafetyCorrect == Spec => []Safety
PROOF OBVIOUS
============================================================================
