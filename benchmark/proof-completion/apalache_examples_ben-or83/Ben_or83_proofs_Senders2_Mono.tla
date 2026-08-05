---- MODULE Ben_or83_proofs_Senders2_Mono ----
EXTENDS Ben_or83_proofs_Senders2_MonoScaffold
THEOREM Senders2_Mono ==
  ASSUME NEW A, NEW B, A \subseteq B
  PROVE  Cardinality(Senders2(A)) <= Cardinality(Senders2(B))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
