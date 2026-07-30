---- MODULE bcastByz_UMFS_CardinalityType ----
EXTENDS bcastByz_UMFS_CardinalityTypeScaffold
THEOREM UMFS_CardinalityType == 
  \A X, Y, Z :    
        /\ IsFiniteSet(X) 
        /\ IsFiniteSet(Y) 
        /\ IsFiniteSet(Z) 
        /\ X \cup Y = Z
        /\ X = Z \ Y
     => Cardinality(X) = Cardinality(Z) - Cardinality(Y)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
