-------------------------- MODULE Allocator_InitTypeInvariant -----------------------------

CONSTANTS
  Client,     
  Resource    

VARIABLES
  unsat,       
  alloc        

TypeInvariant ==
  /\ unsat \in [Client -> SUBSET Resource]
  /\ alloc \in [Client -> SUBSET Resource]

-------------------------------------------------------------------------

Init ==
  /\ unsat = [c \in Client |-> {}]
  /\ alloc = [c \in Client |-> {}]

-------------------------------------------------------------------------

-------------------------------------------------------------------------

-------------------------------------------------------------------------

-------------------------------------------------------------------------

-------------------------------------------------------------------------

THEOREM InitTypeInvariant == Init => TypeInvariant
PROOF
  <1> SUFFICES ASSUME Init
               PROVE  TypeInvariant
    OBVIOUS
  <1>1. \A c \in Client : {} \in SUBSET Resource
    OBVIOUS
  <1>2. [c \in Client |-> {}] \in [Client -> SUBSET Resource]
    BY <1>1
  <1>3. unsat \in [Client -> SUBSET Resource]
    BY <1>2 DEF Init
  <1>4. alloc \in [Client -> SUBSET Resource]
    BY <1>2 DEF Init
  <1> QED
    BY <1>3, <1>4 DEF TypeInvariant

-------------------------------------------------------------------------

=========================================================================
