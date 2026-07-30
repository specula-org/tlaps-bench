---- MODULE Sets_CardinalityZero ----
EXTENDS Sets_CardinalityZeroScaffold
THEOREM CardinalityZero ==
           /\ IsFiniteSet({})
           /\ Cardinality({}) = 0
           /\ \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
