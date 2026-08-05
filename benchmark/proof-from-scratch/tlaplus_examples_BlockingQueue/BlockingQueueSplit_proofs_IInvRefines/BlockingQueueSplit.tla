------------------------- MODULE BlockingQueueSplit -------------------------
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

VARIABLES buffer, waitSetC, waitSetP

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

TypeInv == /\ buffer \in Seq(Producers) 
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSetP \in SUBSET Producers
           /\ waitSetC \in SUBSET Consumers

-----------------------------------------------------------------------------

A == INSTANCE BlockingQueue WITH waitSet <- (waitSetC \cup waitSetP)

=============================================================================
