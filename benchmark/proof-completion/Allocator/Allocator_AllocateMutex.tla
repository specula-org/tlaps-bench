---- MODULE Allocator_AllocateMutex ----
EXTENDS Allocator_AllocateMutexScaffold
THEOREM AllocateMutex ==
  ASSUME NEW clt \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Mutex /\ Allocate(clt, S) => Mutex'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
