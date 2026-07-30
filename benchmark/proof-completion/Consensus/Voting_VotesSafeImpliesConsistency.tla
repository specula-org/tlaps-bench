---- MODULE Voting_VotesSafeImpliesConsistency ----
EXTENDS Voting_VotesSafeImpliesConsistencyScaffold
THEOREM VotesSafeImpliesConsistency ==
   ASSUME VotesSafe, OneVote, chosen # {}
   PROVE  \E v \in Value : chosen = {v}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
