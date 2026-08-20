---- MODULE CRDT_proof_OGLiveness ----
EXTENDS CRDT_proof_OGLivenessDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM OGLiveness == OGSpec => <>(\A n, o \in Node : counter[n] = counter[o])
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
