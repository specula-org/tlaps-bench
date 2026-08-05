---- MODULE tendermint_single_indinv_proofs_QuorumHasCorrect ----
EXTENDS tendermint_single_indinv_proofs_QuorumHasCorrectScaffold
THEOREM QuorumHasCorrect ==
  ASSUME NEW S \in SUBSET (Corr \union Faulty), Cardinality(S) >= 2 * T + 1
  PROVE  \E c \in Corr : c \in S
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
