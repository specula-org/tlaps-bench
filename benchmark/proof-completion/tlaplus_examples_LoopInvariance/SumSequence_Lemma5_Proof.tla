---- MODULE SumSequence_Lemma5_Proof ----
EXTENDS SumSequence_Lemma5_ProofScaffold
LEMMA Lemma5_Proof ==
        \A s \in Seq(Int) : 
          (Len(s) > 0) => 
            SeqSum(s) =  SeqSum(Front(s)) + s[Len(s)]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
