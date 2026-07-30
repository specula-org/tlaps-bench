---- MODULE GraphTheorem_AtLeastTwo ----
EXTENDS GraphTheorem_AtLeastTwoScaffold
THEOREM AtLeastTwo == ASSUME NEW S,
                             IsFiniteSet(S),
                             Cardinality(S) > 1
                      PROVE  \E x, y \in S : x # y
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
