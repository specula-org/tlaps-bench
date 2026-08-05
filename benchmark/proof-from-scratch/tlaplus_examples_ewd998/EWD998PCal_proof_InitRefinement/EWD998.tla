------------------------------- MODULE EWD998 -------------------------------

EXTENDS Integers, FiniteSets, Functions

CONSTANT
    
    N
ASSUME NAssumption == N \in Nat \ {0} 

Node == 0 .. N-1
Color == {"white", "black"}

VARIABLES 
 
 active,     
 
 color,      
 
 counter,    
 
 pending,    
 
 token       

------------------------------------------------------------------------------
 
Init ==
   
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  
  /\ counter = [i \in Node |-> 0] 
  /\ pending = [i \in Node |-> 0]
  /\ token \in [ pos: Node, q: {0}, color: {"black"} ]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

TD == INSTANCE AsyncTerminationDetection

=============================================================================

Checked with TLC in 01/2021 with two cores on a fairly modern desktop
and the given state constraint StateConstraint above:

| N | Diameter | Distinct States | States | Time |
| --- | --- | --- | --- | --- |
| 3 | 60 | 1.3m | 10.1m | 42 s |
| 4 | 105 | 219m | 2.3b | 50 m |
