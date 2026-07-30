---- MODULE BubbleSort_ExchangeAPerm ----
EXTENDS BubbleSort_ExchangeAPermScaffold
THEOREM ExchangeAPerm == \A i, j \in 1..N : Exchange(i, j) \in Perms
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
