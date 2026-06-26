--------------------------- MODULE tcp_proof_InvInit ---------------------------------

EXTENDS tcp, SequenceTheorems, SequencesExtTheorems, FiniteSetTheorems, TLAPS

ASSUME PeersFinite == IsFiniteSet(Peers)

THEOREM InvInit == Init => Inv
PROOF OBVIOUS

============================================================================
