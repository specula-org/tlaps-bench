---- MODULE Euclid_Correctness ----
EXTENDS Euclid_CorrectnessScaffold
USE DEF Number
THEOREM Correctness == Spec => []ResultCorrect
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
