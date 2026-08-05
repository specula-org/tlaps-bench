---- MODULE Ben_or83_proofs_Arith_OtherLtFromStrictOverlap ----
EXTENDS Ben_or83_proofs_Arith_OtherLtFromStrictOverlapScaffold
LEMMA Arith_OtherLtFromStrictOverlap ==
  ASSUME NEW d \in Nat, NEW o \in Nat, NEW i \in Nat, NEW u \in Nat,
         u <= N, u = d + o - i, 2 * d > N + T, i <= F
  PROVE  o < N - 2 * T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
