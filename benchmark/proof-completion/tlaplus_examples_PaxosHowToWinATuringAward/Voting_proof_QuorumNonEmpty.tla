---- MODULE Voting_proof_QuorumNonEmpty ----
EXTENDS Voting_proof_QuorumNonEmptyScaffold
LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
