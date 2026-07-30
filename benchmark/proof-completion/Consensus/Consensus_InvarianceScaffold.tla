----------------------------- MODULE Consensus_InvarianceScaffold ------------------------------
EXTENDS ConsensusModel

Inv == 
    /\ chosen \subseteq Value
    /\ IsFiniteSet(chosen)
    /\ Cardinality(chosen) \leq 1
=============================================================================
