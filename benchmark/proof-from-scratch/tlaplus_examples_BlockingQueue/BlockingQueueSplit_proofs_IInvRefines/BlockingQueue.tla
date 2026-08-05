--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   
          Consumers,   
          BufCapacity  

ASSUME Assumption ==
       /\ Producers # {}                      
       /\ Consumers # {}                      
       /\ Producers \intersect Consumers = {} 
       /\ BufCapacity \in (Nat \ {0})         
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \in SUBSET (Producers \cup Consumers)

Invariant == waitSet # (Producers \cup Consumers)

-----------------------------------------------------------------------------

IInv == /\ TypeInv!2
        /\ TypeInv!3
        /\ Invariant

        /\ buffer = <<>> => \E p \in Producers : p \notin waitSet

        /\ Len(buffer) = BufCapacity => \E c \in Consumers : c \notin waitSet

-----------------------------------------------------------------------------

=============================================================================
