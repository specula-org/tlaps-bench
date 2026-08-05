---- MODULE tendermint_single_indinv_proofs_PastStartRoundQuorumMonotone ----
EXTENDS tendermint_single_indinv_proofs_PastStartRoundQuorumMonotoneScaffold
LEMMA PastStartRoundQuorumMonotone ==
  ASSUME IndTypeOk, Step, NEW R \in (0)..(MaxRound), R # 0,
         \/ Cardinality(PVAll(R) \union PCAll(R)) >= T + 1
         \/ Cardinality(PCAll(R - 1)) >= 2 * T + 1
  PROVE  \/ Cardinality(PVAllP(R) \union PCAllP(R)) >= T + 1
         \/ Cardinality(PCAllP(R - 1)) >= 2 * T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
