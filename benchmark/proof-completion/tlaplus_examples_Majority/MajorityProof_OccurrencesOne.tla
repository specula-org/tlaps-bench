---- MODULE MajorityProof_OccurrencesOne ----
EXTENDS MajorityProof_OccurrencesOneScaffold
LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
