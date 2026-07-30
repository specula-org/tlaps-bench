---- MODULE CRDT_proof_MeasureIsZero ----
EXTENDS CRDT_proof_MeasureIsZeroScaffold
LEMMA MeasureIsZero ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : Distance(o) = 0 
                 <=> \A n \in Node : counter[o][n] = counter[n][n]
         /\ Measure = 0
            <=> \A v,w,n \in Node : counter[v][n] = counter[w][n]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
