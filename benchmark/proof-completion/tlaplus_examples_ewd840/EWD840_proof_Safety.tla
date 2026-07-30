---- MODULE EWD840_proof_Safety ----
EXTENDS EWD840_proof_SafetyScaffold
USE NAssumption
THEOREM Safety == Spec => []TerminationDetection
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
