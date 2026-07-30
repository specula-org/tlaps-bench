---- MODULE SimpleRegular_Correctness ----
EXTENDS SimpleRegular_CorrectnessScaffold
THEOREM Correctness == Spec => []PCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
