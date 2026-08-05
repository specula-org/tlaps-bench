---- MODULE LamportMutex_proofs_BoundedNetworkInv ----
EXTENDS LamportMutex_proofs_BoundedNetworkInvDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM BoundedNetworkInv == Spec => []BoundedNetwork
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
