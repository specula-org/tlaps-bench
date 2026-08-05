---- MODULE Ben_or83_proofs_Senders1_Sub ----
EXTENDS Ben_or83_proofs_Senders1_SubScaffold
THEOREM Senders1_Sub ==
  ASSUME NEW S
  PROVE  Senders1(S) \subseteq ALL /\ IsFiniteSet(Senders1(S))
        /\ Cardinality(Senders1(S)) <= N
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
