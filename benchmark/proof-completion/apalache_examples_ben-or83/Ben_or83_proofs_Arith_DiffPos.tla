---- MODULE Ben_or83_proofs_Arith_DiffPos ----
EXTENDS Ben_or83_proofs_Arith_DiffPosScaffold
LEMMA Arith_DiffPos ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a >= T + 1, b <= F
  PROVE  a - b >= 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
