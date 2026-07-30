---- MODULE Voting_Refinement ----
EXTENDS Voting_RefinementScaffold
THEOREM Refinement == Spec => C!Spec
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
