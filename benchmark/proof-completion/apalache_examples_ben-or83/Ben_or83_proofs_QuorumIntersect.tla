---- MODULE Ben_or83_proofs_QuorumIntersect ----
EXTENDS Ben_or83_proofs_QuorumIntersectScaffold
THEOREM QuorumIntersect ==
  ASSUME NEW QA, NEW QB,
         QA \subseteq ALL, QB \subseteq ALL,
         Cardinality(QA) >= N - T, Cardinality(QB) >= N - T
  PROVE  /\ Cardinality(QA \cap QB) >= N - 2 * T
         /\ \E id \in QA \cap QB : id \in CORRECT
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
