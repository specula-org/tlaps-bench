---- MODULE stages_proof_NatMinNat ----
EXTENDS stages_proof_NatMinNatScaffold
LEMMA NatMinNat ==
  ASSUME NEW i \in Nat, NEW j \in Nat
  PROVE  natMin(i, j) \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
