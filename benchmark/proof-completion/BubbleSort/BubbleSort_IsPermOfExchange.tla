---- MODULE BubbleSort_IsPermOfExchange ----
EXTENDS BubbleSort_IsPermOfExchangeScaffold
THEOREM IsPermOfExchange == 
           \A A \in [1..N -> Int],  i, j \in 1..N :
             /\ [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
             /\ IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
