---- MODULE AllocatorImplementation_proof_DropType ----
EXTENDS AllocatorImplementation_proof_DropTypeScaffold
LEMMA DropType ==
  ASSUME NEW T, NEW s \in Seq(T), NEW i \in 1..Len(s)
  PROVE  Sched!Drop(s, i) \in Seq(T)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
