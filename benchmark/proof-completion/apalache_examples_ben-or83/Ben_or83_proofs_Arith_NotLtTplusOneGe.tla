---- MODULE Ben_or83_proofs_Arith_NotLtTplusOneGe ----
EXTENDS Ben_or83_proofs_Arith_NotLtTplusOneGeScaffold
LEMMA Arith_NotLtTplusOneGe ==
  ASSUME NEW a \in Nat, ~(a < T + 1)
  PROVE  a >= T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
