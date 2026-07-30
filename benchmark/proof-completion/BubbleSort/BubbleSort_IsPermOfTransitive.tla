---- MODULE BubbleSort_IsPermOfTransitive ----
EXTENDS BubbleSort_IsPermOfTransitiveScaffold
THEOREM IsPermOfTransitive == 
          \A A, B, C \in [1..N -> Int] : 
             IsPermOf(A, B) /\ IsPermOf(B, C) => IsPermOf(A, C)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
