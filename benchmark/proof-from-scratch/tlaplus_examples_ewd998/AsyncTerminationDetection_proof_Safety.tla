---- MODULE AsyncTerminationDetection_proof_Safety ----
EXTENDS AsyncTerminationDetection_proof_SafetyDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Safety == Init /\ [][Next]_vars => []Safe
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
