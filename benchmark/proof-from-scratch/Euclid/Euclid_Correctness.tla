---- MODULE Euclid_Correctness ----
EXTENDS Euclid_CorrectnessDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Correctness == Spec => []ResultCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
