--------------------------- MODULE SpanTree_proof_TypeCorrect -----------------------------

EXTENDS SpanTree, TLAPS

ASSUME ConstantsAssumption ==
  /\ Root \in Nodes
  /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
  /\ MaxCardinality \in Nat
  /\ MaxCardinality >= Cardinality(Nodes)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS
============================================================================
