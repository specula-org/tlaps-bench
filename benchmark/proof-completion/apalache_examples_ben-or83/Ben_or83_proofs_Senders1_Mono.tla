---- MODULE Ben_or83_proofs_Senders1_Mono ----
EXTENDS Ben_or83_proofs_Senders1_MonoScaffold
THEOREM Senders1_Mono ==
  ASSUME NEW A, NEW B, A \subseteq B
  PROVE  Cardinality(Senders1(A)) <= Cardinality(Senders1(B))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
