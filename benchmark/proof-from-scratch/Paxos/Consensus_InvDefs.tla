----------------------------- MODULE Consensus_InvDefs -----------------------------

EXTENDS ConsensusModel

Inv == Cardinality(chosen) <= 1

=============================================================================

