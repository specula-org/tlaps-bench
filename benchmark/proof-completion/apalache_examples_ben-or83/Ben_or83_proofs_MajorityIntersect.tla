---- MODULE Ben_or83_proofs_MajorityIntersect ----
EXTENDS Ben_or83_proofs_MajorityIntersectScaffold
THEOREM MajorityIntersect ==
  ASSUME NEW QA, NEW QB, QA \subseteq ALL, QB \subseteq ALL,
         2 * Cardinality(QA) > N + T, 2 * Cardinality(QB) > N + T
  PROVE  \E id \in QA \cap QB : id \in CORRECT
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
