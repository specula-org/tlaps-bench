---- MODULE LamportMutex_proofs_BoundedNetworkInv ----
EXTENDS LamportMutex_proofs_BoundedNetworkInvScaffold
USE DEF Clock
THEOREM BoundedNetworkInv == Spec => []BoundedNetwork
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
