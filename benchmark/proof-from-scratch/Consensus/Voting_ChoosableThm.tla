---- MODULE Voting_ChoosableThm ----
EXTENDS Voting_ChoosableThmDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value :
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
