---- MODULE Paxos_QuorumNonEmpty ----
EXTENDS Paxos_QuorumNonEmptyScaffold
LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
