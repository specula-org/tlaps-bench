---- MODULE Sets_CardinalityOne ----
EXTENDS Sets_CardinalityOneScaffold
THEOREM CardinalityOne == \A m : /\ IsFiniteSet({m})
                                 /\ Cardinality({m}) = 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
