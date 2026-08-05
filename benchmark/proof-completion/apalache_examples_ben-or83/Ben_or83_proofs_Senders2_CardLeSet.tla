---- MODULE Ben_or83_proofs_Senders2_CardLeSet ----
EXTENDS Ben_or83_proofs_Senders2_CardLeSetScaffold
THEOREM Senders2_CardLeSet ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  Cardinality(Senders2(S)) <= Cardinality(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
