---- MODULE Ben_or83_proofs_Arith_DoubleGtNplusTImplGt3T ----
EXTENDS Ben_or83_proofs_Arith_DoubleGtNplusTImplGt3TScaffold
LEMMA Arith_DoubleGtNplusTImplGt3T ==
  ASSUME NEW d \in Nat, 2 * d > N + T
  PROVE  d > 3 * T
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
