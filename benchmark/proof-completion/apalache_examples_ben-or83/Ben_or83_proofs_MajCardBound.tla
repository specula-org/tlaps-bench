---- MODULE Ben_or83_proofs_MajCardBound ----
EXTENDS Ben_or83_proofs_MajCardBoundScaffold
THEOREM MajCardBound ==
  ASSUME NEW QA, NEW QB, QA \subseteq ALL, QB \subseteq ALL,
         2 * Cardinality(QA) > N + T, 2 * Cardinality(QB) > N + T
  PROVE  Cardinality(QA \cap QB) >= T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
