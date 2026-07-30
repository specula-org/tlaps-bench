---- MODULE Simple_Correctness ----
EXTENDS Simple_CorrectnessScaffold
THEOREM Correctness == Spec => []PCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
