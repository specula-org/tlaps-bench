--------------------------- MODULE tcp_proof_TypeCorrectDefs ---------------------------------

EXTENDS tcp, SequenceTheorems, SequencesExtTheorems, FiniteSetTheorems, TLAPS

ASSUME PeersFinite == IsFiniteSet(Peers)

============================================================================
