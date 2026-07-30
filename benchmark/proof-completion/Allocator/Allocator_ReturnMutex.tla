---- MODULE Allocator_ReturnMutex ----
EXTENDS Allocator_ReturnMutexScaffold
THEOREM ReturnMutex ==
  ASSUME NEW clt \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Mutex /\ Return(clt,S) => Mutex'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
