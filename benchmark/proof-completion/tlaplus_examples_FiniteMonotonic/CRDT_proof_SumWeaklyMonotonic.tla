---- MODULE CRDT_proof_SumWeaklyMonotonic ----
EXTENDS CRDT_proof_SumWeaklyMonotonicScaffold
LEMMA SumWeaklyMonotonic ==
  ASSUME NEW f \in [Node -> Nat], NEW g \in [Node -> Nat],
         \A x \in Node : f[x] <= g[x]
  PROVE  Sum(f) <= Sum(g)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
