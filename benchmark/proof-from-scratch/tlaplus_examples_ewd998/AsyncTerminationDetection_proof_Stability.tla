---- MODULE AsyncTerminationDetection_proof_Stability ----
EXTENDS AsyncTerminationDetection_proof_StabilityDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Stability == Init /\ [][Next]_vars => Quiescence
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
