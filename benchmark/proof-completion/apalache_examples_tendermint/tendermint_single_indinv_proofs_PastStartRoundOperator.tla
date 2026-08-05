---- MODULE tendermint_single_indinv_proofs_PastStartRoundOperator ----
EXTENDS tendermint_single_indinv_proofs_PastStartRoundOperatorScaffold
LEMMA PastStartRoundOperator ==
  ASSUME IndTypeOk, AllPastStartRound, NEW c \in Corr, NEW R \in (0)..(MaxRound),
         ~(R > round[c]), R # 0
  PROVE  \/ Cardinality(PVAll(R) \union PCAll(R)) >= T + 1
         \/ Cardinality(PCAll(R - 1)) >= 2 * T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
