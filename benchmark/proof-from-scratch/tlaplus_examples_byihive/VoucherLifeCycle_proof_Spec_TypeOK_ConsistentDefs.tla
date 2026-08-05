------------------------ MODULE VoucherLifeCycle_proof_Spec_TypeOK_ConsistentDefs ----------------------

EXTENDS VoucherLifeCycle, TLAPS

Inv == VTypeOK /\ VConsistent

============================================================================
