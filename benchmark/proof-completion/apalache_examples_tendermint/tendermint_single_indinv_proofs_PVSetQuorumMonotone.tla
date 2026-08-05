---- MODULE tendermint_single_indinv_proofs_PVSetQuorumMonotone ----
EXTENDS tendermint_single_indinv_proofs_PVSetQuorumMonotoneScaffold
LEMMA PVSetQuorumMonotone ==
  ASSUME IndTypeOk, Step, NEW r \in (0)..(MaxRound),
         NEW d \in ((ValidValues \union InvalidValues) \union {-1}),
         Cardinality(PVSet(r, d)) >= 2 * T + 1
  PROVE  Cardinality(PVSetP(r, d)) >= 2 * T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
