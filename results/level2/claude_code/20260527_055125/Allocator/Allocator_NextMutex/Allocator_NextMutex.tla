-------------------------- MODULE Allocator_NextMutex -----------------------------

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

Mutex ==
  \A c1,c2 \in Client : \A r \in Resource :
     r \in alloc[c1] \cap alloc[c2] => c1 = c2

-------------------------------------------------------------------------

-------------------------------------------------------------------------

-------------------------------------------------------------------------

-------------------------------------------------------------------------

THEOREM NextMutex == TypeInvariant /\ Mutex /\ Next => Mutex'
<1> SUFFICES ASSUME TypeInvariant, Mutex, Next
             PROVE  Mutex'
  OBVIOUS
<1>2. alloc \in [Client -> SUBSET Resource]
  BY DEF TypeInvariant
<1>3. PICK c \in Client, S \in SUBSET Resource :
           Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
  BY DEF Next
<1>4. CASE Request(c,S)
  BY <1>4 DEF Request, Mutex
<1>5. CASE Allocate(c,S)
  <2> SUFFICES ASSUME NEW c1 \in Client, NEW c2 \in Client, NEW r \in Resource,
                      r \in alloc'[c1] \cap alloc'[c2]
               PROVE  c1 = c2
    BY DEF Mutex
  <2>2. alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    BY <1>5 DEF Allocate
  <2>3. S \subseteq available
    BY <1>5 DEF Allocate
  <2>4. r \in S => (\A d \in Client : r \notin alloc[d])
    BY <2>3, <1>2 DEF available
  <2>5. r \in alloc[c1] \/ (c1 = c /\ r \in S)
    BY <2>2, <1>2
  <2>6. r \in alloc[c2] \/ (c2 = c /\ r \in S)
    BY <2>2, <1>2
  <2>7. QED
    BY <2>4, <2>5, <2>6 DEF Mutex
<1>6. CASE Return(c,S)
  BY <1>6, <1>2 DEF Return, Mutex
<1>7. QED
  BY <1>3, <1>4, <1>5, <1>6

=========================================================================
