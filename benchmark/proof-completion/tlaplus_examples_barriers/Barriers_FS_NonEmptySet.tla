---- MODULE Barriers_FS_NonEmptySet ----
EXTENDS Barriers_FS_NonEmptySetScaffold
THEOREM FS_NonEmptySet ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE Cardinality(S) > 0 <=> \E x: x \in S
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
