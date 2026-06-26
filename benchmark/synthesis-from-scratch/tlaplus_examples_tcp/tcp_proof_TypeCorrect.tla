--------------------------- MODULE tcp_proof_TypeCorrect ---------------------------------

EXTENDS tcp, SequenceTheorems, SequencesExtTheorems, FiniteSetTheorems, TLAPS

ASSUME PeersFinite == IsFiniteSet(Peers)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

============================================================================
