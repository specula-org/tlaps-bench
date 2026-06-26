------------------- MODULE SyncTerminationDetection_proof_Live -------------------

EXTENDS SyncTerminationDetection, TLAPS

------------------------------------------------------------------------------

THEOREM Live == Spec => Liveness
PROOF OBVIOUS

=============================================================================
