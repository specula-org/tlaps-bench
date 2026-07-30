---- MODULE AllocatorImplementation_proof_PermSeqsType ----
EXTENDS AllocatorImplementation_proof_PermSeqsTypeScaffold
LEMMA PermSeqsType ==
  ASSUME NEW T, NEW S \in SUBSET T, IsFiniteSet(S),
         NEW sq \in Sched!PermSeqs(S)
  PROVE  sq \in Seq(T)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
