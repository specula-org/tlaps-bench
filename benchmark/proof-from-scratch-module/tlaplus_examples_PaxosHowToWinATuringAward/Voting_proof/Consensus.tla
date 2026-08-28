----------------------------- MODULE Consensus ------------------------------ 

EXTENDS Naturals, FiniteSets, TLAPS, FiniteSetTheorems

CONSTANT Value 

VARIABLE chosen

TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen) 

-----------------------------------------------------------------------------

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

=============================================================================
