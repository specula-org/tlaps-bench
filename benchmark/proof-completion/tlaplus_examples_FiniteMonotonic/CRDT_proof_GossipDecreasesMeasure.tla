---- MODULE CRDT_proof_GossipDecreasesMeasure ----
EXTENDS CRDT_proof_GossipDecreasesMeasureScaffold
LEMMA GossipDecreasesMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         <<\E n,o \in Node : Gossip(n,o)>>_vars
  PROVE  Measure' < Measure
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
