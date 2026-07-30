---- MODULE SumSequence_Lemma2a ----
EXTENDS SumSequence_Lemma2aScaffold
LEMMA Lemma2a ==
  ASSUME NEW S, NEW s \in Seq(S), Len(s) > 1
  PROVE  Tail(s) = [i \in 1..(Len(s) - 1) |-> s[i+1]]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
