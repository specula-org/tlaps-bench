---- MODULE CRDT_proof_OGLiveness ----
EXTENDS CRDT_proof_OGLivenessScaffold
THEOREM OGLiveness == OGSpec => <>(\A n, o \in Node : counter[n] = counter[o])
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
