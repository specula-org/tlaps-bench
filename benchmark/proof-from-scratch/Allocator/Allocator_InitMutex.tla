---- MODULE Allocator_InitMutex ----
EXTENDS Allocator_InitMutexDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM InitMutex == Init => Mutex
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
