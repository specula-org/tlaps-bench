------------------------------- MODULE CRDT_proof_OGLiveness ---------------------------------
EXTENDS CRDT_proof

THEOREM OGLiveness == OGSpec => <>(\A n, o \in Node : counter[n] = counter[o])
PROOF OBVIOUS

=============================================================================
