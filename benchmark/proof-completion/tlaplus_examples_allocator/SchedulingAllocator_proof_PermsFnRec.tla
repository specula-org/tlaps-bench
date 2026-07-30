---- MODULE SchedulingAllocator_proof_PermsFnRec ----
EXTENDS SchedulingAllocator_proof_PermsFnRecScaffold
LEMMA PermsFnRec ==
  ASSUME NEW S, IsFiniteSet(S), NEW ss \in SUBSET S
  PROVE  PermsFn(S)[ss] = PermsRec(PermsFn(S), ss)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
