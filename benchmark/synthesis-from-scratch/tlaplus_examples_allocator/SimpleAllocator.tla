------------------------ MODULE SimpleAllocator -------------------------

EXTENDS FiniteSets, TLC

CONSTANTS
  Clients,     
  Resources    

ASSUME
  IsFiniteSet(Resources)

VARIABLES
  unsat,       
  alloc        

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

-------------------------------------------------------------------------

available == Resources \ (UNION {alloc[c] : c \in Clients})

Init == 
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

Request(c,S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

Allocate(c,S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

Return(c,S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

Next == 
  \E c \in Clients, S \in SUBSET Resources :
     Request(c,S) \/ Allocate(c,S) \/ Return(c,S)

vars == <<unsat,alloc>>

-------------------------------------------------------------------------

SimpleAllocator == 
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients: WF_vars(Return(c, alloc[c]))
  /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

-------------------------------------------------------------------------

ResourceMutex ==
  \A c1,c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

ClientsWillReturn ==
  \A c \in Clients : unsat[c]={} ~> alloc[c]={}

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]

InfOftenSatisfied == 
  \A c \in Clients : []<>(unsat[c] = {})

-------------------------------------------------------------------------

Symmetry == Permutations(Clients) \cup Permutations(Resources)

-------------------------------------------------------------------------

SimpleAllocator2 == 
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients: WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

-------------------------------------------------------------------------

THEOREM SimpleAllocator => []TypeInvariant
  PROOF OMITTED

THEOREM SimpleAllocator => []ResourceMutex
  PROOF OMITTED

THEOREM SimpleAllocator => ClientsWillReturn
  PROOF OMITTED

THEOREM SimpleAllocator2 => ClientsWillReturn
  PROOF OMITTED

THEOREM SimpleAllocator => ClientsWillObtain
  PROOF OMITTED

THEOREM SimpleAllocator => InfOftenSatisfied
  PROOF OMITTED

=========================================================================
