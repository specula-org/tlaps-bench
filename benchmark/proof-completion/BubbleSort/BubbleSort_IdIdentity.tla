---- MODULE BubbleSort_IdIdentity ----
EXTENDS BubbleSort_IdIdentityScaffold
THEOREM IdIdentity == \A A \in [1..N -> Int] : A ** Id = A
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
