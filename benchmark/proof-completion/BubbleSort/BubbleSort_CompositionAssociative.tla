---- MODULE BubbleSort_CompositionAssociative ----
EXTENDS BubbleSort_CompositionAssociativeScaffold
THEOREM CompositionAssociative == 
           \A A \in [1..N -> Int], f, g \in [1..N -> 1..N] :
                (A ** f) ** g  =  A ** (f ** g)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
