-------------------------- MODULE two_thread_mutex_LivenessDefs -------------------------
EXTENDS two_thread_mutexModel

BothThreadsTerminated ==
  \A tid \in Tid : threads[tid] = "Terminated"

Termination ==
  <>BothThreadsTerminated

=============================================================================
