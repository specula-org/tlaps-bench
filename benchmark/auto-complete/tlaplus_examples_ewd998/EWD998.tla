------------------------------- MODULE EWD998 -------------------------------

EXTENDS Integers, FiniteSets, Functions

CONSTANT
    
    N
ASSUME NAssumption == N \in Nat \ {0} 

Node == 0 .. N-1
Color == {"white", "black"}
Token == [pos : Node, q : Int, color : Color]

VARIABLES 
 
 active,     
 
 color,      
 
 counter,    
 
 pending,    
 
 token       
  
vars == <<active, color, counter, pending, token>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in Token
------------------------------------------------------------------------------
 
Init ==
   
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  
  /\ counter = [i \in Node |-> 0] 
  /\ pending = [i \in Node |-> 0]
  /\ token \in [ pos: Node, q: {0}, color: {"black"} ]

InitiateProbe ==
  
  /\ token.pos = 0
  /\ 
     \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [ color EXCEPT ![0] = "white" ]
  
  /\ UNCHANGED <<active, counter, pending>>                            
  
PassToken(i) ==
  
  /\ ~ active[i] 
  /\ token.pos = i
  /\ token' = [pos |-> token.pos - 1,
               q |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
            
  /\ color' = [ color EXCEPT ![i] = "white" ]
  
  /\ UNCHANGED <<active, counter, pending>>

System == \/ InitiateProbe
          \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
  
  /\ active[i]
  
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  
  /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]

  /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  
  /\ color' = [ color EXCEPT ![i] = "black" ]
  
  /\ active' = [ active EXCEPT ![i] = TRUE ]
  /\ UNCHANGED <<token>>                           

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

StateConstraint ==
  /\ \A i \in Node : counter[i] <= 3 /\ pending[i] <= 3
  /\ token.q <= 9

-----------------------------------------------------------------------------

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

Sum(f, S) == FoldFunctionOnSet(+, 0, f, S)

B == Sum(pending, Node)

Termination == 
  /\ \A i \in Node : ~ active[i]
  /\ B = 0

TerminationDetection ==
  terminationDetected => Termination

Rng(a,b) == { i \in Node: a <= i /\ i <= b }

Inv == 
  
  /\ P0:: B = Sum(counter, Node)

  /\ \/ P1:: /\ \A i \in Rng(token.pos+1, N-1): active[i] = FALSE 
             /\ IF token.pos = N-1 
                THEN token.q = 0 
                ELSE token.q = Sum(counter, Rng(token.pos+1,N-1))
     
     \/ P2:: Sum(counter, Rng(0, token.pos)) + token.q > 0
     
     \/ P3:: \E i \in Rng(0, token.pos) : color[i] = "black"
     
     \/ P4:: token.color = "black"

TypedInv ==
    /\ TypeOK
    /\ Inv

Liveness ==
  Termination ~> terminationDetected

TD == INSTANCE AsyncTerminationDetection

TDSpec == TD!Spec

THEOREM Spec => TDSpec
  PROOF OMITTED

=============================================================================

Checked with TLC in 01/2021 with two cores on a fairly modern desktop
and the given state constraint StateConstraint above:

| N | Diameter | Distinct States | States | Time |
| --- | --- | --- | --- | --- |
| 3 | 60 | 1.3m | 10.1m | 42 s |
| 4 | 105 | 219m | 2.3b | 50 m |
