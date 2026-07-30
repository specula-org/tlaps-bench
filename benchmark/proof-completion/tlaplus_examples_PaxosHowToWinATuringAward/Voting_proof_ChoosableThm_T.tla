---- MODULE Voting_proof_ChoosableThm_T ----
EXTENDS Voting_proof_ChoosableThm_TScaffold
THEOREM ChoosableThm_T ==
    \A b \in Ballot, v \in Value : ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
