---- MODULE Sets_CardinalityTwo ----
EXTENDS Sets_CardinalityTwoDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM CardinalityTwo == \A m, p : m # p => 
                              /\ IsFiniteSet({m,p})
                              /\ Cardinality({m,p}) = 2
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
