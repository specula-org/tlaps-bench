---- MODULE tendermint_single_indinv_proofs_Q3UnionMonotone ----
EXTENDS tendermint_single_indinv_proofs_Q3UnionMonotoneScaffold
LEMMA Q3UnionMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality(PVAll(r) \union PCAll(r)) <= Cardinality(PVAllP(r) \union PCAllP(r))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
