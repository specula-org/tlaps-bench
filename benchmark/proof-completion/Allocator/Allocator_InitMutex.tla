---- MODULE Allocator_InitMutex ----
EXTENDS Allocator_InitMutexScaffold
THEOREM InitMutex == Init => Mutex
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
