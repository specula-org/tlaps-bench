---- MODULE Ben_or83_proofs_FaultyBound ----
EXTENDS Ben_or83_proofs_FaultyBoundScaffold
THEOREM FaultyBound ==
  ASSUME NEW S, S \subseteq ALL
  PROVE  Cardinality(S \cap FAULTY) <= F
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
