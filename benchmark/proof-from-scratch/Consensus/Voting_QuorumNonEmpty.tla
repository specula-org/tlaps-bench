---- MODULE Voting_QuorumNonEmpty ----
EXTENDS Voting_QuorumNonEmptyDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
