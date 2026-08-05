---- MODULE Ben_or83_proofs_Lemma3_Q2D2Faulty ----
EXTENDS Ben_or83_proofs_Lemma3_Q2D2FaultyScaffold
THEOREM Lemma3_Q2D2Faulty ==
  ASSUME Lemma3_NoEquivocation2ByCorrect,
         NEW r \in ROUNDS,
         NEW mq \in msgs2[r], NEW md \in msgs2[r],
         IsQ2(mq), IsD2(md), AsQ2(mq).src = AsD2(md).src
  PROVE  AsQ2(mq).src \in FAULTY
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
