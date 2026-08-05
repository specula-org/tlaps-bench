----------------------------- MODULE Consensus_LivenessTheoremDefs ------------------------------
EXTENDS ConsensusModel

Success == <>(chosen # {})
LiveSpec == Spec /\ WF_chosen(Next)  

=============================================================================
