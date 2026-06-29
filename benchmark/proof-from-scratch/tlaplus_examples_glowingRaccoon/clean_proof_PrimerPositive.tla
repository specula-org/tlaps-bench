--------------------------- MODULE clean_proof_PrimerPositive --------------------------------

EXTENDS clean, TLAPS

ASSUME ConstantsAreNat == DNA \in Nat /\ PRIMER \in Nat

THEOREM PrimerPositive == Spec => []primerPositive
PROOF OBVIOUS

============================================================================
