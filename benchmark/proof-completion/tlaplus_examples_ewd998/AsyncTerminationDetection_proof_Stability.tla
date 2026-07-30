---- MODULE AsyncTerminationDetection_proof_Stability ----
EXTENDS AsyncTerminationDetection_proof_StabilityScaffold
THEOREM Stability == Init /\ [][Next]_vars => Quiescence
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
