---- MODULE SyncTerminationDetection_proof_Enabled_ST ----
EXTENDS SyncTerminationDetection_proof_Enabled_STScaffold
LEMMA Enabled_ST == 
    ASSUME TypeOK
    PROVE (ENABLED <<DetectTermination>>_vars) <=> terminated /\ ~terminationDetected
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
