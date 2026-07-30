---- MODULE VoteProof_InductiveInvariance ----
EXTENDS VoteProof_InductiveInvarianceScaffold
THEOREM InductiveInvariance == VInv /\ [Next]_vars => VInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
