---- MODULE EWD998_proof_TerminationDetectionInv ----
EXTENDS EWD998_proof_TerminationDetectionInvScaffold
USE NAssumption
THEOREM TerminationDetectionInv == Spec => []TerminationDetection
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
