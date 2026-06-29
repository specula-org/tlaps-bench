--------------------------- MODULE CoffeeCan_proof_TypeCorrect ----------------------------

EXTENDS CoffeeCan, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS
============================================================================
