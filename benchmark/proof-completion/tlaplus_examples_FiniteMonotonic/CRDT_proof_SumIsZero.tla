---- MODULE CRDT_proof_SumIsZero ----
EXTENDS CRDT_proof_SumIsZeroScaffold
LEMMA SumIsZero ==
  ASSUME NEW f \in [Node -> Nat]
  PROVE  Sum(f) = 0 <=> \A x \in Node : f[x] = 0
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
