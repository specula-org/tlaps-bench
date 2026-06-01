-------------------------- MODULE Allocator_NextTypeInvariant -----------------------------

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

available == Resource \ (UNION {alloc[c] : c \in Client})

Request(c,S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

Allocate(c,S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]

Return(c,S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
  /\ UNCHANGED unsat

Next ==
  \E c \in Client, S \in SUBSET Resource :
     Request(c,S) \/ Allocate(c,S) \/ Return(c,S)

-------------------------------------------------------------------------

-------------------------------------------------------------------------

-------------------------------------------------------------------------

-------------------------------------------------------------------------

-------------------------------------------------------------------------

THEOREM NextTypeInvariant == TypeInvariant /\ Next => TypeInvariant'
<1> SUFFICES ASSUME TypeInvariant, Next
             PROVE TypeInvariant'
  OBVIOUS
<1>1. PICK c \in Client, S \in SUBSET Resource :
         Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
  BY DEF Next
<1>2. /\ unsat \in [Client -> SUBSET Resource]
      /\ alloc \in [Client -> SUBSET Resource]
  BY DEF TypeInvariant
<1>3. CASE Request(c,S)
  <2>1. unsat' = [unsat EXCEPT ![c] = S]
    BY <1>3 DEF Request
  <2>2. alloc' = alloc
    BY <1>3 DEF Request
  <2> QED
    BY <2>1, <2>2, <1>2 DEF TypeInvariant
<1>4. CASE Allocate(c,S)
  <2>1. unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    BY <1>4 DEF Allocate
  <2>2. alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    BY <1>4 DEF Allocate
  <2>3. unsat[c] \ S \in SUBSET Resource
    BY <1>2
  <2>4. alloc[c] \cup S \in SUBSET Resource
    BY <1>2
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <1>2 DEF TypeInvariant
<1>5. CASE Return(c,S)
  <2>1. unsat' = unsat
    BY <1>5 DEF Return
  <2>2. alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    BY <1>5 DEF Return
  <2>3. alloc[c] \ S \in SUBSET Resource
    BY <1>2
  <2> QED
    BY <2>1, <2>2, <2>3, <1>2 DEF TypeInvariant
<1>6. QED
  BY <1>1, <1>3, <1>4, <1>5

-------------------------------------------------------------------------

=========================================================================
