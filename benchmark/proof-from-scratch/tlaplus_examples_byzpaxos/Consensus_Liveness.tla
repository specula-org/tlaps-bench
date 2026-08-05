---- MODULE Consensus_Liveness ----
EXTENDS Consensus_LivenessDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Liveness == LiveSpec => Success
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
