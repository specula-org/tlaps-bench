---- MODULE SimpleRegular_Correctness ----
EXTENDS SimpleRegular_CorrectnessDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Correctness == Spec => []PCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
