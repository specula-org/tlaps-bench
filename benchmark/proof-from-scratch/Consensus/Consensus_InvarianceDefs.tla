----------------------------- MODULE Consensus_InvarianceDefs ------------------------------
EXTENDS ConsensusModel

Inv == 
    /\ chosen \subseteq Value
    /\ IsFiniteSet(chosen)
    /\ Cardinality(chosen) \leq 1
=============================================================================
