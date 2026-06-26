--------------------------- MODULE stages_proof_TypeCorrect -------------------------------

EXTENDS stages, TLAPS

ASSUME ConstantsAreNat == DNA \in Nat /\ PRIMER \in Nat

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS
============================================================================
