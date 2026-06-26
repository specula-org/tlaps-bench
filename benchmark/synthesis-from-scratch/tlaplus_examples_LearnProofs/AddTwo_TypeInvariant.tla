------------------------------ MODULE AddTwo_TypeInvariant --------------------------------

EXTENDS AddTwo

TypeOK == x \in Nat

THEOREM TypeInvariant == Spec => []TypeOK
PROOF OBVIOUS

=============================================================================

