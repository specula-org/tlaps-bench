---- MODULE tcp_proof_PeersAB ----
EXTENDS tcp_proof_PeersABScaffold
LEMMA PeersAB ==
  /\ A \in Peers
  /\ B \in Peers
  /\ A # B
  /\ Peers = {A, B}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
