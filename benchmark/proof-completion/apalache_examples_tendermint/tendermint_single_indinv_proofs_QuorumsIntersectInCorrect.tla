---- MODULE tendermint_single_indinv_proofs_QuorumsIntersectInCorrect ----
EXTENDS tendermint_single_indinv_proofs_QuorumsIntersectInCorrectScaffold
THEOREM QuorumsIntersectInCorrect ==
  ASSUME NEW A \in SUBSET (Corr \union Faulty),
         NEW B \in SUBSET (Corr \union Faulty),
         Cardinality(A) >= 2 * T + 1,
         Cardinality(B) >= 2 * T + 1
  PROVE  \E c \in Corr : c \in A /\ c \in B
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
