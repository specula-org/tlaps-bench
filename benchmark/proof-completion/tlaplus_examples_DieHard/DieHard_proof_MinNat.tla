---- MODULE DieHard_proof_MinNat ----
EXTENDS DieHard_proof_MinNatScaffold
LEMMA MinNat ==
  ASSUME NEW m \in Nat, NEW n \in Nat
  PROVE  Min(m, n) \in Nat /\ Min(m, n) <= m /\ Min(m, n) <= n
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
