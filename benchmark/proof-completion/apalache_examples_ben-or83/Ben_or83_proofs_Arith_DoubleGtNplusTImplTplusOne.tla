---- MODULE Ben_or83_proofs_Arith_DoubleGtNplusTImplTplusOne ----
EXTENDS Ben_or83_proofs_Arith_DoubleGtNplusTImplTplusOneScaffold
LEMMA Arith_DoubleGtNplusTImplTplusOne ==
  ASSUME NEW a \in Nat, 2 * a > N + T
  PROVE  a >= T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
