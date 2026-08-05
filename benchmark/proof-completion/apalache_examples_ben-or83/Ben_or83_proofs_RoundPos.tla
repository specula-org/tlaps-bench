---- MODULE Ben_or83_proofs_RoundPos ----
EXTENDS Ben_or83_proofs_RoundPosScaffold
THEOREM RoundPos ==
  ASSUME NEW r \in ROUNDS
  PROVE  r \in Nat /\ r >= 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
