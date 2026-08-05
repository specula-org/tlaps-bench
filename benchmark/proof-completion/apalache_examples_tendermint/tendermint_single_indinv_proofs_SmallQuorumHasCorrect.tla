---- MODULE tendermint_single_indinv_proofs_SmallQuorumHasCorrect ----
EXTENDS tendermint_single_indinv_proofs_SmallQuorumHasCorrectScaffold
LEMMA SmallQuorumHasCorrect ==
  ASSUME NEW S \in SUBSET (Corr \union Faulty), Cardinality(S) >= T + 1
  PROVE  \E c \in Corr : c \in S
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
