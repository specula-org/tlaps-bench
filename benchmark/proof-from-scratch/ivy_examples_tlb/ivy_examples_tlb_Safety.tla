--------------------------- MODULE ivy_examples_tlb_Safety ---------------------------
EXTENDS IvyTlb

NoError ==
  ~error

THEOREM Safety == SafetySpec => []NoError
PROOF OBVIOUS

=============================================================================
