---- MODULE Ben_or83_proofs_CardUnion2LeSum ----
EXTENDS Ben_or83_proofs_CardUnion2LeSumScaffold
THEOREM CardUnion2LeSum ==
  ASSUME NEW A, NEW B, IsFiniteSet(A), IsFiniteSet(B)
  PROVE  Cardinality(A \union B) <= Cardinality(A) + Cardinality(B)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
