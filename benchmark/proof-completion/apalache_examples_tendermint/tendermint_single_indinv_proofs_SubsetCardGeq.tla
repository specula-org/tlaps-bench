---- MODULE tendermint_single_indinv_proofs_SubsetCardGeq ----
EXTENDS tendermint_single_indinv_proofs_SubsetCardGeqScaffold
LEMMA SubsetCardGeq ==
  ASSUME NEW A, NEW B, A \subseteq B, IsFiniteSet(B), NEW k \in Nat, Cardinality(A) >= k
  PROVE  Cardinality(B) >= k
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
