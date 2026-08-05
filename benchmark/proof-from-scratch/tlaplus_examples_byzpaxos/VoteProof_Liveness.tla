---- MODULE VoteProof_Liveness ----
EXTENDS VoteProof_LivenessDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Liveness == LiveSpec => C!LiveSpec
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
