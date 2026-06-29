--------------------------- MODULE Voting_proof_ChoosableThm_T ----------------------------

EXTENDS Voting

THEOREM ChoosableThm_T ==
    \A b \in Ballot, v \in Value : ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
PROOF OBVIOUS

============================================================================
