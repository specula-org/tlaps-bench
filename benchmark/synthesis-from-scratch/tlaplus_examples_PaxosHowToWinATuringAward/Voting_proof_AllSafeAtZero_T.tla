--------------------------- MODULE Voting_proof_AllSafeAtZero_T ----------------------------

EXTENDS Voting

THEOREM AllSafeAtZero_T == \A v \in Value : SafeAt(0, v)
PROOF OBVIOUS

============================================================================
