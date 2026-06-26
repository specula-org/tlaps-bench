--------------------------- MODULE Voting_proof_ShowsSafety_T ----------------------------

EXTENDS Voting

THEOREM ShowsSafety_T ==
    Inv => \A Q \in Quorum, b \in Ballot, v \in Value :
              ShowsSafeAt(Q, b, v) => SafeAt(b, v)
PROOF OBVIOUS

============================================================================
