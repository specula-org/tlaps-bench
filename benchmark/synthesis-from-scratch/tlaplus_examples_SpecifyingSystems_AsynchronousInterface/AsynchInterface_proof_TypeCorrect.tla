------------------------ MODULE AsynchInterface_proof_TypeCorrect ----------------------

EXTENDS AsynchInterface, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
PROOF OBVIOUS

============================================================================
