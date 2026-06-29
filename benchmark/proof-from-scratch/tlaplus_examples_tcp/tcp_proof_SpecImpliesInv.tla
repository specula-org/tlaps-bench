--------------------------- MODULE tcp_proof_SpecImpliesInv ---------------------------------

EXTENDS tcp, SequenceTheorems, SequencesExtTheorems, FiniteSetTheorems, TLAPS

ASSUME PeersFinite == IsFiniteSet(Peers)

THEOREM SpecImpliesInv == Spec => []Inv
PROOF OBVIOUS
============================================================================
