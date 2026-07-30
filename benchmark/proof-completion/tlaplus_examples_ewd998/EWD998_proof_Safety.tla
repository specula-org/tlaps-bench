---- MODULE EWD998_proof_Safety ----
EXTENDS EWD998_proof_SafetyScaffold
USE NAssumption
THEOREM Safety ==
  /\ TypeOK /\ Inv /\ terminationDetected => Termination
  /\ TypeOK' /\ Inv' /\ terminationDetected' => Termination'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
