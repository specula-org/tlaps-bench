------------------------ MODULE VoucherLifeCycle_proof_Spec_TypeOK_Consistent ----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*    THEOREM VSpec => [](VTypeOK /\ VConsistent)                          *)
(* stated in VoucherLifeCycle.tla.  TypeOK and VConsistent together form   *)
(* an inductive invariant.                                                 *)
(***************************************************************************)
EXTENDS VoucherLifeCycle, TLAPS

Inv == VTypeOK /\ VConsistent

THEOREM Spec_TypeOK_Consistent == VSpec => []Inv
PROOF OBVIOUS

============================================================================
