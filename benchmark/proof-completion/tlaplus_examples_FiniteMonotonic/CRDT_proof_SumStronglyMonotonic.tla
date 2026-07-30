---- MODULE CRDT_proof_SumStronglyMonotonic ----
EXTENDS CRDT_proof_SumStronglyMonotonicScaffold
LEMMA SumStronglyMonotonic ==
  ASSUME NEW f \in [Node -> Nat], NEW g \in [Node -> Nat],
         \A x \in Node : f[x] <= g[x],
         \E x \in Node : f[x] < g[x]
  PROVE  Sum(f) < Sum(g)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
