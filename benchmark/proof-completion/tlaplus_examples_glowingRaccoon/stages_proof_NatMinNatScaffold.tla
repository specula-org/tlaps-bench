--------------------------- MODULE stages_proof_NatMinNatScaffold -------------------------------
(***************************************************************************)
(* TLAPS proof of the type-correctness invariant of stages.tla.            *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(***************************************************************************)
EXTENDS stages, TLAPS

ASSUME ConstantsAreNat == DNA \in Nat /\ PRIMER \in Nat

=============================================================================
