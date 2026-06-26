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
vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

NotifyOther(Others) == 
    IF waitSet \cap Others # {}
    THEN \E t \in waitSet \cap Others : waitSet' = waitSet \ {t}
    ELSE UNCHANGED waitSet

Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
/\ t \notin waitSet
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(Consumers)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
      
Get(t) ==
/\ t \notin waitSet
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(Producers)
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

Init == /\ buffer = <<>>
        /\ waitSet = {}

Next == \/ \E p \in Producers: Put(p, p) 
        \/ \E c \in Consumers: Get(c)

-----------------------------------------------------------------------------

TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \in SUBSET (Producers \cup Consumers)

Invariant == waitSet # (Producers \cup Consumers)

-----------------------------------------------------------------------------

MySeq(P) == UNION {[1..n -> P] : n \in 0..BufCapacity}

Spec == Init /\ [][Next]_vars

IInv == /\ TypeInv!2
        /\ TypeInv!3
        /\ Invariant

        /\ buffer = <<>> => \E p \in Producers : p \notin waitSet

        /\ Len(buffer) = BufCapacity => \E c \in Consumers : c \notin waitSet

MCIInv == TypeInv!1 /\ IInv

-----------------------------------------------------------------------------

PutEnabled == \A p \in Producers : ENABLED Put(p, p)

FairSpec == 
    /\ Spec

    /\ \A t \in Producers:
            WF_vars(Put(t,t)) 

    /\ \A t \in Producers:
            SF_vars(\E self \in Consumers: Get(self) /\ t \notin waitSet')

    /\ \A t \in Consumers:
            WF_vars(Get(t)) 
    /\ \A t \in Consumers:
            SF_vars(\E self \in Producers: Put(self, self) /\ t \notin waitSet')

Starvation ==
    /\ \A p \in Producers: []<>(<<Put(p, p)>>_vars)
    /\ \A c \in Consumers: []<>(<<Get(c)>>_vars)

=============================================================================
