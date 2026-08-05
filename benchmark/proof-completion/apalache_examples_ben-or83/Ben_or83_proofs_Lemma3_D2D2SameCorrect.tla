---- MODULE Ben_or83_proofs_Lemma3_D2D2SameCorrect ----
EXTENDS Ben_or83_proofs_Lemma3_D2D2SameCorrectScaffold
THEOREM Lemma3_D2D2SameCorrect ==
  ASSUME Lemma3_NoEquivocation2ByCorrect,
         NEW r \in ROUNDS,
         NEW m1 \in msgs2[r], NEW m2 \in msgs2[r],
         IsD2(m1), IsD2(m2), AsD2(m1).src = AsD2(m2).src,
         AsD2(m1).src \in CORRECT
  PROVE  AsD2(m1).v = AsD2(m2).v
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
