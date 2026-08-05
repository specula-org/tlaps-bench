-------------------------- MODULE Allocator_InitTypeInvariantDefs -----------------------------

CONSTANTS
  Client,     
  Resource    

VARIABLES
  unsat,       
  alloc        

TypeInvariant ==
  /\ unsat \in [Client -> SUBSET Resource]
  /\ alloc \in [Client -> SUBSET Resource]

Init ==
  /\ unsat = [c \in Client |-> {}]
  /\ alloc = [c \in Client |-> {}]

=========================================================================
