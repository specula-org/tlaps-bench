---- MODULE PaxosCommit_proof_MaximumProp ----
EXTENDS PaxosCommit_proof_MaximumPropScaffold
LEMMA MaximumProp ==
  ASSUME NEW S, IsFiniteSet(S), S \subseteq Int, S # {},
         \A x \in S : x >= -1
  PROVE  /\ Maximum(S) \in S
         /\ \A n \in S : n =< Maximum(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
