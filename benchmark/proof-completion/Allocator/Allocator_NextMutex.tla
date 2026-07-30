---- MODULE Allocator_NextMutex ----
EXTENDS Allocator_NextMutexScaffold
THEOREM NextMutex == TypeInvariant /\ Mutex /\ Next => Mutex'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
