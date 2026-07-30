---- MODULE Sets_CardinalityInNat ----
EXTENDS Sets_CardinalityInNatScaffold
THEOREM CardinalityInNat == \A S : IsFiniteSet(S) => Cardinality(S) \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
