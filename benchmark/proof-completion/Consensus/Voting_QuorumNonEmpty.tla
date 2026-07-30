---- MODULE Voting_QuorumNonEmpty ----
EXTENDS Voting_QuorumNonEmptyScaffold
THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
