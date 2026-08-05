----------------------------- MODULE Consensus_LivenessDefs ------------------------------

EXTENDS ConsensusModel

LiveSpec == Spec /\ WF_vars(Next)
Success == <>(chosen # {})

=============================================================================
