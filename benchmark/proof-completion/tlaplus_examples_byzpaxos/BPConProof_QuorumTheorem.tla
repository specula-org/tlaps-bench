---- MODULE BPConProof_QuorumTheorem ----
EXTENDS BPConProof_QuorumTheoremScaffold
THEOREM QuorumTheorem ==
         /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
         /\ \A Q \in Quorum : Q \subseteq Acceptor
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
