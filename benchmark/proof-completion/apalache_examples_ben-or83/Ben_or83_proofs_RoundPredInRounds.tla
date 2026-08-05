---- MODULE Ben_or83_proofs_RoundPredInRounds ----
EXTENDS Ben_or83_proofs_RoundPredInRoundsScaffold
LEMMA RoundPredInRounds ==
  ASSUME NEW r \in ROUNDS, r # 1
  PROVE  r - 1 \in ROUNDS
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
