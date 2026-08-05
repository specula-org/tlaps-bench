---- MODULE Ben_or83_proofs_Arith_NotAllFaulty ----
EXTENDS Ben_or83_proofs_Arith_NotAllFaultyScaffold
LEMMA Arith_NotAllFaulty ==
  ASSUME NEW a \in Nat, a >= N - 2 * T, a <= F
  PROVE  FALSE
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
