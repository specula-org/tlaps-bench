---- MODULE bcastByz_ProcProp ----
EXTENDS bcastByz_ProcPropScaffold
THEOREM ProcProp == Cardinality(Proc) = N /\ IsFiniteSet(Proc) /\ Cardinality(Proc) \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
