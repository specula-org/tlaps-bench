---- MODULE Ben_or83_proofs_Arith_TplusOneNotFaulty ----
EXTENDS Ben_or83_proofs_Arith_TplusOneNotFaultyScaffold
LEMMA Arith_TplusOneNotFaulty ==
  ASSUME NEW a \in Nat, a >= T + 1, a <= F
  PROVE  FALSE
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
