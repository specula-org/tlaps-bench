---- MODULE Euclid_NextProperty ----
EXTENDS Euclid_NextPropertyScaffold
USE DEF Number
THEOREM NextProperty == InductiveInvariant /\ Next => InductiveInvariant'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
