---- MODULE CRDT_proof_Safe ----
EXTENDS CRDT_proof_SafeScaffold
THEOREM Safe == Spec => []Safety
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
