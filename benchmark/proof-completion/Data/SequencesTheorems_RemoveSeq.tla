---- MODULE SequencesTheorems_RemoveSeq ----
EXTENDS SequencesTheorems_RemoveSeqScaffold
THEOREM RemoveSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE   Remove(i, seq) \in Seq(S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
