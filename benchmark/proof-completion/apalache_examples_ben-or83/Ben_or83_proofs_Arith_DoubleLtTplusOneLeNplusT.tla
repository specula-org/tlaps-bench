---- MODULE Ben_or83_proofs_Arith_DoubleLtTplusOneLeNplusT ----
EXTENDS Ben_or83_proofs_Arith_DoubleLtTplusOneLeNplusTScaffold
LEMMA Arith_DoubleLtTplusOneLeNplusT ==
  ASSUME NEW a \in Nat, a < T + 1
  PROVE  2 * a <= N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
