---- MODULE CRDT_proof_MeasureType ----
EXTENDS CRDT_proof_MeasureTypeScaffold
LEMMA MeasureType ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : DistFun(o) \in [Node -> Nat]
         /\ \A o \in Node : Distance(o) \in Nat
         /\ Measure \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
