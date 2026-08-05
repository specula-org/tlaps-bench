---- MODULE AsyncTerminationDetection_proof_Liveness ----
EXTENDS AsyncTerminationDetection_proof_LivenessDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Liveness == Spec => Live
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
