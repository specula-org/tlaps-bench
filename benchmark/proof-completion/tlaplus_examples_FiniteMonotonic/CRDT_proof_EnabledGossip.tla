---- MODULE CRDT_proof_EnabledGossip ----
EXTENDS CRDT_proof_EnabledGossipScaffold
LEMMA EnabledGossip ==
  ASSUME NEW n \in Node, NEW o \in Node, TypeOK
  PROVE  (ENABLED <<Gossip(n,o)>>_vars) <=>
         \E v \in Node : counter[o][v] < counter[n][v]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
