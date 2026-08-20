---- MODULE two_thread_mutex_Liveness ----
EXTENDS two_thread_mutex_LivenessDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Liveness == Spec => Termination
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
