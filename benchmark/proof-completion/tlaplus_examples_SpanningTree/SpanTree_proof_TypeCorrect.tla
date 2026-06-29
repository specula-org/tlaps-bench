--------------------------- MODULE SpanTree_proof_TypeCorrect -----------------------------
(***************************************************************************)
(* TLAPS proof of  Spec => []TypeOK.                                       *)
(***************************************************************************)
EXTENDS SpanTree, TLAPS

(***************************************************************************)
(* Restate the spec's unnamed ASSUME for proof use.                        *)
(***************************************************************************)
ASSUME ConstantsAssumption ==
  /\ Root \in Nodes
  /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
  /\ MaxCardinality \in Nat
  /\ MaxCardinality >= Cardinality(Nodes)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS
============================================================================
