---- MODULE Allocator_NextMutex ----
EXTENDS Allocator_NextMutexDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM NextMutex == TypeInvariant /\ Mutex /\ Next => Mutex'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
