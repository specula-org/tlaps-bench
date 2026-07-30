---- MODULE CRDT_proof_MeasureTypePrime ----
EXTENDS CRDT_proof_MeasureTypePrimeScaffold
LEMMA MeasureTypePrime ==
  ASSUME TypeOK', Safety'
  PROVE  /\ \A o \in Node : DistFun(o)' \in [Node -> Nat]
         /\ \A o \in Node : Distance(o)' \in Nat
         /\ Measure' \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
