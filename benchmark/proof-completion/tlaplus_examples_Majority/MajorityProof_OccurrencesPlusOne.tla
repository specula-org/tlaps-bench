---- MODULE MajorityProof_OccurrencesPlusOne ----
EXTENDS MajorityProof_OccurrencesPlusOneScaffold
LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
