---- MODULE AsyncTerminationDetection_proof_EnabledDT ----
EXTENDS AsyncTerminationDetection_proof_EnabledDTScaffold
LEMMA EnabledDT == 
  ASSUME TypeOK 
  PROVE  (ENABLED <<DetectTermination>>_vars) <=> (terminated /\ ~ terminationDetected)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
