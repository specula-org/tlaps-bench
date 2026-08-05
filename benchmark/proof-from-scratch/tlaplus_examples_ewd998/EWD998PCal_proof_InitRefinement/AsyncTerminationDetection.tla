---------------------- MODULE AsyncTerminationDetection ---------------------

EXTENDS Naturals
CONSTANT
  
  N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES 
  
  active,               
  
  pending,              
  
  terminationDetected   

terminated == \A n \in Node : ~ active[n] /\ pending[n] = 0

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending = [n \in Node |-> 0]
  /\ terminationDetected \in {FALSE, terminated}

=============================================================================

