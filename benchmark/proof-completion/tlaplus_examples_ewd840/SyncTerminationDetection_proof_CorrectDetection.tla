---- MODULE SyncTerminationDetection_proof_CorrectDetection ----
EXTENDS SyncTerminationDetection_proof_CorrectDetectionScaffold
THEOREM CorrectDetection == Spec => TDCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
