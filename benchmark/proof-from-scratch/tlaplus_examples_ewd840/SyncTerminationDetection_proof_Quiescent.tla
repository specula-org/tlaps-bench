------------------- MODULE SyncTerminationDetection_proof_Quiescent -------------------

EXTENDS SyncTerminationDetection, TLAPS

THEOREM Quiescent == Spec => Quiescence
PROOF OBVIOUS

------------------------------------------------------------------------------

=============================================================================
