---- MODULE Simple_Correctness2 ----
EXTENDS Simple_Correctness2Defs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Correctness2 == Spec => []PCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
