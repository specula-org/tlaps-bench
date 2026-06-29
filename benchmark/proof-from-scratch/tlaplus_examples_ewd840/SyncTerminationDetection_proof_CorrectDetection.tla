------------------- MODULE SyncTerminationDetection_proof_CorrectDetection -------------------

EXTENDS SyncTerminationDetection, TLAPS

THEOREM CorrectDetection == Spec => TDCorrect
PROOF OBVIOUS

------------------------------------------------------------------------------

=============================================================================
