---- MODULE Voting_proof_QuorumIntersect ----
EXTENDS Voting_proof_QuorumIntersectScaffold
LEMMA QuorumIntersect ==
  ASSUME NEW Q1 \in Quorum, NEW Q2 \in Quorum
  PROVE  \E a \in Q1 \cap Q2 : a \in Acceptor
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
