---- MODULE SumSequence_Lemma3 ----
EXTENDS SumSequence_Lemma3Scaffold
LEMMA Lemma3 ==
  \A S : \A s \in Seq(S) :
            (Len(s) > 1) => (Tail(Front(s)) = Front(Tail(s)))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
