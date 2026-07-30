---- MODULE MajorityProof_OccurrencesType ----
EXTENDS MajorityProof_OccurrencesTypeScaffold
LEMMA OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v,j) \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
