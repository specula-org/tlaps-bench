---- MODULE Ben_or83_proofs_Arith_DoubleLeFromNotGtMono ----
EXTENDS Ben_or83_proofs_Arith_DoubleLeFromNotGtMonoScaffold
LEMMA Arith_DoubleLeFromNotGtMono ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a <= b, ~(2 * b > N + T)
  PROVE  2 * a <= N + T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
