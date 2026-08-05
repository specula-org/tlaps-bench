---- MODULE SimpleRegular_Correctness2 ----
EXTENDS SimpleRegular_Correctness2Defs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Correctness2 == Spec => []PCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
