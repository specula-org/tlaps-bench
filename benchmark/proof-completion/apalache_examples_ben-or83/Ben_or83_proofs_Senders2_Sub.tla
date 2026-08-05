---- MODULE Ben_or83_proofs_Senders2_Sub ----
EXTENDS Ben_or83_proofs_Senders2_SubScaffold
THEOREM Senders2_Sub ==
  ASSUME NEW S
  PROVE  Senders2(S) \subseteq ALL /\ IsFiniteSet(Senders2(S))
        /\ Cardinality(Senders2(S)) <= N
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
