---- MODULE CRDT_proof_SumIsSumFunction ----
EXTENDS CRDT_proof_SumIsSumFunctionScaffold
LEMMA SumIsSumFunction ==
  ASSUME NEW f
  PROVE  Sum(f) = SumFunction(f)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
