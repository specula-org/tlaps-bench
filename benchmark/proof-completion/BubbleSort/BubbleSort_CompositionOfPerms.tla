---- MODULE BubbleSort_CompositionOfPerms ----
EXTENDS BubbleSort_CompositionOfPermsScaffold
THEOREM CompositionOfPerms == \A f, g \in Perms : f ** g \in Perms
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
