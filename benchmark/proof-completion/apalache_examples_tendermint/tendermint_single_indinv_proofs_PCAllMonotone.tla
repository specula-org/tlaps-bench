---- MODULE tendermint_single_indinv_proofs_PCAllMonotone ----
EXTENDS tendermint_single_indinv_proofs_PCAllMonotoneScaffold
LEMMA PCAllMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound)
  PROVE  Cardinality(PCAll(r)) <= Cardinality(PCAllP(r))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
