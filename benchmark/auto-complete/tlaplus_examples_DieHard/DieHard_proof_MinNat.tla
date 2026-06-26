--------------------------- MODULE DieHard_proof_MinNat ------------------------------
(***************************************************************************)
(* TLAPS proof of  Spec => []TypeOK.                                       *)
(* (NotSolved is meant to be violated -- it's the puzzle's "find a         *)
(*  solution" search invariant -- so we don't try to prove it.)            *)
(***************************************************************************)
EXTENDS DieHard, TLAPS

LEMMA MinNat ==
  ASSUME NEW m \in Nat, NEW n \in Nat
  PROVE  Min(m, n) \in Nat /\ Min(m, n) <= m /\ Min(m, n) <= n
PROOF OBVIOUS

============================================================================
