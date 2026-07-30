---- MODULE SumSequence_Lemma2 ----
EXTENDS SumSequence_Lemma2Scaffold
LEMMA Lemma2 == 
       \A S : \A s \in Seq(S) :
          Len(s) > 0 => /\ Tail(s) \in Seq(S)
                        /\ Front(s) \in Seq(S)
                        /\ Len(Tail(s)) = Len(s) - 1
                        /\ Len(Front(s)) = Len(s) - 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
