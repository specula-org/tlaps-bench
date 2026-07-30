---- MODULE VoteProof_Liveness ----
EXTENDS VoteProof_LivenessScaffold
THEOREM Liveness == LiveSpec => C!LiveSpec
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
