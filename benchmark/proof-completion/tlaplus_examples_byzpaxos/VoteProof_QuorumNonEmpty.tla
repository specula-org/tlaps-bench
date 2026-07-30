---- MODULE VoteProof_QuorumNonEmpty ----
EXTENDS VoteProof_QuorumNonEmptyScaffold
THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
