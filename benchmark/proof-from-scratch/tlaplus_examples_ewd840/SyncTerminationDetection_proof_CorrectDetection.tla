---- MODULE SyncTerminationDetection_proof_CorrectDetection ----
EXTENDS SyncTerminationDetection_proof_CorrectDetectionDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM CorrectDetection == Spec => TDCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
