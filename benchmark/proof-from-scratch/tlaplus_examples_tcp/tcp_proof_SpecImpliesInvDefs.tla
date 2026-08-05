--------------------------- MODULE tcp_proof_SpecImpliesInvDefs ---------------------------------

EXTENDS tcp, SequenceTheorems, SequencesExtTheorems, FiniteSetTheorems, TLAPS

ASSUME PeersFinite == IsFiniteSet(Peers)

============================================================================
