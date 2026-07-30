---- MODULE TPaxosWithProof_MaxBigger ----
EXTENDS TPaxosWithProof_MaxBiggerScaffold
LEMMA MaxBigger == \A a \in Ballot \cup {-1}, b \in Ballot: Max(a, b) >= a /\ Max(a, b) >= b
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
