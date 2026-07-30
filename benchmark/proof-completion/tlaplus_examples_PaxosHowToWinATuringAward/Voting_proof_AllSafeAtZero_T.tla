---- MODULE Voting_proof_AllSafeAtZero_T ----
EXTENDS Voting_proof_AllSafeAtZero_TScaffold
THEOREM AllSafeAtZero_T == \A v \in Value : SafeAt(0, v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
