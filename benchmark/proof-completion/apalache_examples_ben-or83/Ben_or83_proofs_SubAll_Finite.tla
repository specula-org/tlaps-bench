---- MODULE Ben_or83_proofs_SubAll_Finite ----
EXTENDS Ben_or83_proofs_SubAll_FiniteScaffold
THEOREM SubAll_Finite ==
  ASSUME NEW Q, Q \subseteq ALL
  PROVE  IsFiniteSet(Q) /\ Cardinality(Q) <= N
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
