---- MODULE Ben_or83_proofs_Arith_DoubleNotGtLe ----
EXTENDS Ben_or83_proofs_Arith_DoubleNotGtLeScaffold
LEMMA Arith_DoubleNotGtLe ==
  ASSUME NEW a \in Nat, ~(2 * a > N + T)
  PROVE  2 * a <= N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
