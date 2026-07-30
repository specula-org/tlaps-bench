---- MODULE CRDT_proof_SumType ----
EXTENDS CRDT_proof_SumTypeScaffold
LEMMA SumType ==
  ASSUME NEW f \in [Node -> Nat]
  PROVE  Sum(f) \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
