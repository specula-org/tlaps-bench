---- MODULE BubbleSort_line202 ----
EXTENDS BubbleSort_line202Defs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Spec => [](pc = "Done" => IsSorted(A) /\ IsPermOf(A, A0))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
