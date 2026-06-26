------------------------ MODULE VoucherLifeCycle_proof_Spec_TypeOK_Consistent ----------------------

EXTENDS VoucherLifeCycle, TLAPS

Inv == VTypeOK /\ VConsistent

THEOREM Spec_TypeOK_Consistent == VSpec => []Inv
PROOF OBVIOUS

============================================================================
