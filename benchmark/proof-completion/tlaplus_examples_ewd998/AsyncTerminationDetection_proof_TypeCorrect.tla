---- MODULE AsyncTerminationDetection_proof_TypeCorrect ----
EXTENDS AsyncTerminationDetection_proof_TypeCorrectScaffold
LEMMA TypeCorrect == Init /\ [][Next]_vars => []TypeOK
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
