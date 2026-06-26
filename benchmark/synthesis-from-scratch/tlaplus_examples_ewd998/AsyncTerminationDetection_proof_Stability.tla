---------------------- MODULE AsyncTerminationDetection_proof_Stability ---------------------

EXTENDS AsyncTerminationDetection, TLAPS

THEOREM Stability == Init /\ [][Next]_vars => Quiescence
PROOF OBVIOUS

=============================================================================

