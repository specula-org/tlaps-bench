---- MODULE Voting_AllSafeAtZero ----
EXTENDS Voting_AllSafeAtZeroScaffold
THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
