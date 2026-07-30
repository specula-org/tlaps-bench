------------------------ MODULE VoucherLifeCycle_proof_Spec_TypeOK_ConsistentScaffold ----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*    THEOREM VSpec => [](VTypeOK /\ VConsistent)                          *)
(* stated in VoucherLifeCycle.tla.  TypeOK and VConsistent together form   *)
(* an inductive invariant.                                                 *)
(***************************************************************************)
EXTENDS VoucherLifeCycle, TLAPS

Inv == VTypeOK /\ VConsistent

=============================================================================
