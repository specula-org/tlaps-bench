---- MODULE CRDT_proof_GossipDoesntIncreaseMeasure ----
EXTENDS CRDT_proof_GossipDoesntIncreaseMeasureScaffold
LEMMA GossipDoesntIncreaseMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         [\E n,o \in Node : Gossip(n,o)]_vars
  PROVE  /\ \A v,w \in Node : DistFun(v)'[w] <= DistFun(v)[w]
         /\ \A v \in Node : Distance(v)' <= Distance(v)
         /\ Measure' <= Measure
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
