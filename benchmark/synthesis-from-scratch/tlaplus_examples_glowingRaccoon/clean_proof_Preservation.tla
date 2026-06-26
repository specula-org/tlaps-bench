--------------------------- MODULE clean_proof_Preservation --------------------------------

EXTENDS clean, TLAPS

ASSUME ConstantsAreNat == DNA \in Nat /\ PRIMER \in Nat

THEOREM Preservation == Spec => []preservationInvariant
PROOF OBVIOUS
============================================================================
