---------------------- MODULE AsyncTerminationDetection_proof_Safety ---------------------

EXTENDS AsyncTerminationDetection, TLAPS

THEOREM Safety == Init /\ [][Next]_vars => []Safe
PROOF OBVIOUS

=============================================================================

