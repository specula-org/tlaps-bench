---- MODULE Consensus_Liveness ----
EXTENDS Consensus_LivenessScaffold
THEOREM Liveness == LiveSpec => Success
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
