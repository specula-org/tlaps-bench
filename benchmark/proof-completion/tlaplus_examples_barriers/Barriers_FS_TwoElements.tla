---- MODULE Barriers_FS_TwoElements ----
EXTENDS Barriers_FS_TwoElementsScaffold
THEOREM FS_TwoElements ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE Cardinality(S) > 1 => \E x, y \in S: x # y
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
