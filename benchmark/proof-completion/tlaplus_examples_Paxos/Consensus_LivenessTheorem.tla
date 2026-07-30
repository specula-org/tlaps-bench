---- MODULE Consensus_LivenessTheorem ----
EXTENDS Consensus_LivenessTheoremScaffold
THEOREM LivenessTheorem == LiveSpec =>  Success
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
