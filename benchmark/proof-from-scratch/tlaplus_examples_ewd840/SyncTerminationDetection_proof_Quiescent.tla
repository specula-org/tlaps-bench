---- MODULE SyncTerminationDetection_proof_Quiescent ----
EXTENDS SyncTerminationDetection_proof_QuiescentDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Quiescent == Spec => Quiescence
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
