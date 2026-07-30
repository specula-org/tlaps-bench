---- MODULE SchedulingAllocator_proof_PermSeqsIsPermsFn ----
EXTENDS SchedulingAllocator_proof_PermSeqsIsPermsFnScaffold
LEMMA PermSeqsIsPermsFn ==
  ASSUME NEW S
  PROVE  PermSeqs(S) = PermsFn(S)[S]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
