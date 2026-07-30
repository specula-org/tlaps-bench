---- MODULE SumSequence_Lemma1_Proof ----
EXTENDS SumSequence_Lemma1_ProofScaffold
LEMMA Lemma1_Proof ==
         \A s \in Seq(Int) : 
          SeqSum(s) = IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
