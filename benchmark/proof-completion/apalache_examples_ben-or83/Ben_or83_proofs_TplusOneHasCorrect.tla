---- MODULE Ben_or83_proofs_TplusOneHasCorrect ----
EXTENDS Ben_or83_proofs_TplusOneHasCorrectScaffold
THEOREM TplusOneHasCorrect ==
  ASSUME NEW S, S \subseteq ALL, Cardinality(S) >= T + 1
  PROVE  \E id \in S : id \in CORRECT
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
