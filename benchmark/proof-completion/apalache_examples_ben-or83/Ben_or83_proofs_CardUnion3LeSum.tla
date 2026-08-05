---- MODULE Ben_or83_proofs_CardUnion3LeSum ----
EXTENDS Ben_or83_proofs_CardUnion3LeSumScaffold
THEOREM CardUnion3LeSum ==
  ASSUME NEW A, NEW B, NEW C,
         IsFiniteSet(A), IsFiniteSet(B), IsFiniteSet(C)
  PROVE  Cardinality((A \union B) \union C)
           <= Cardinality(A) + Cardinality(B) + Cardinality(C)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
