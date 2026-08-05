---- MODULE Consensus_LivenessTheorem ----
EXTENDS Consensus_LivenessTheoremDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM LivenessTheorem == LiveSpec =>  Success
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
