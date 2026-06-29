---------------------- MODULE AsyncTerminationDetection_proof_Liveness ---------------------

EXTENDS AsyncTerminationDetection, TLAPS

THEOREM Liveness == Spec => Live
PROOF OBVIOUS

=============================================================================

