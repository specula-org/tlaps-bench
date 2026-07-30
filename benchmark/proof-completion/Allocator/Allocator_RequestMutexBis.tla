---- MODULE Allocator_RequestMutexBis ----
EXTENDS Allocator_RequestMutexBisScaffold
THEOREM RequestMutexBis ==
  ASSUME NEW clt \in Client,
         NEW S \in SUBSET Resource
  PROVE  Mutex /\ Request(clt,S) => Mutex'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
