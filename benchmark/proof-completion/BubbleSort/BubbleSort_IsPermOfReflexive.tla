---- MODULE BubbleSort_IsPermOfReflexive ----
EXTENDS BubbleSort_IsPermOfReflexiveScaffold
THEOREM IsPermOfReflexive == \A A \in [1..N -> Int]  : IsPermOf(A, A)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
