---- MODULE EWD998_proof_Detection ----
EXTENDS EWD998_proof_DetectionScaffold
USE NAssumption
LEMMA Detection == 
  TypeOK /\ Inv /\ Termination /\ atMaster /\ allWhite /\ tknWhite /\ tknCount
    => terminationDetected
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
