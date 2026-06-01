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

Fresh(S) ==
  \A c \in Client : \A r \in S : r \notin alloc[c]

LEMMA AvailableFresh ==
  ASSUME NEW S \in SUBSET Resource,
         S \subseteq available
  PROVE  Fresh(S)
PROOF
<1>1. SUFFICES ASSUME NEW c \in Client,
                      NEW r \in S
               PROVE  r \notin alloc[c]
  BY DEF Fresh
<1>2. r \in Resource
  BY <1>1
<1>3. r \notin UNION {alloc[d] : d \in Client}
  BY <1>1, <1>2 DEF available
<1>4. alloc[c] \in {alloc[d] : d \in Client}
  BY <1>1
<1>. QED
  BY <1>3, <1>4

LEMMA RequestPreservesMutex ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource,
         Mutex,
         Request(c,S)
  PROVE  Mutex'
PROOF
<1>1. alloc' = alloc
  BY DEF Request
<1>. QED
  BY <1>1 DEF Mutex

LEMMA ReturnPreservesMutex ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource,
         TypeInvariant,
         Mutex,
         Return(c,S)
  PROVE  Mutex'
PROOF
<1>1. alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
  BY DEF Return
<1>2. \A d \in Client : alloc'[d] \subseteq alloc[d]
  <2>1. SUFFICES ASSUME NEW d \in Client
                 PROVE  alloc'[d] \subseteq alloc[d]
    OBVIOUS
  <2>2. CASE d = c
    BY <1>1, <2>1 DEF TypeInvariant
  <2>3. CASE d # c
    BY <1>1, <2>1 DEF TypeInvariant
  <2>. QED
    BY <2>2, <2>3
<1>3. SUFFICES ASSUME NEW c1 \in Client,
                      NEW c2 \in Client,
                      NEW r \in Resource,
                      r \in alloc'[c1] \cap alloc'[c2]
               PROVE  c1 = c2
  BY DEF Mutex
<1>4. r \in alloc[c1] /\ r \in alloc[c2]
  BY <1>2, <1>3
<1>. QED
  BY <1>3, <1>4 DEF Mutex

LEMMA AllocatePreservesMutex ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource,
         TypeInvariant,
         Mutex,
         Allocate(c,S)
  PROVE  Mutex'
PROOF
<1>1. alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
  BY DEF Allocate
<1>2. S \subseteq available
  BY DEF Allocate
<1>3. Fresh(S)
  BY <1>2, AvailableFresh
<1>4. SUFFICES ASSUME NEW c1 \in Client,
                      NEW c2 \in Client,
                      NEW r \in Resource,
                      r \in alloc'[c1] \cap alloc'[c2]
               PROVE  c1 = c2
  BY DEF Mutex
<1>5. CASE c1 = c2
  BY <1>5
<1>6. CASE c1 # c2
  <2>1. CASE c1 = c
    <3>1. c2 # c
      BY <1>6, <2>1
    <3>2. r \in alloc[c] \/ r \in S
      BY <1>1, <1>4, <2>1 DEF TypeInvariant
    <3>3. r \in alloc[c2]
      BY <1>1, <1>4, <3>1 DEF TypeInvariant
    <3>4. CASE r \in alloc[c]
      BY <1>4, <2>1, <3>3, <3>4 DEF Mutex
    <3>5. CASE r \in S
      BY <1>3, <1>4, <3>3, <3>5 DEF Fresh
    <3>. QED
      BY <3>2, <3>4, <3>5
  <2>2. CASE c2 = c
    <3>1. c1 # c
      BY <1>6, <2>2
    <3>2. r \in alloc[c] \/ r \in S
      BY <1>1, <1>4, <2>2 DEF TypeInvariant
    <3>3. r \in alloc[c1]
      BY <1>1, <1>4, <3>1 DEF TypeInvariant
    <3>4. CASE r \in alloc[c]
      BY <1>4, <2>2, <3>3, <3>4 DEF Mutex
    <3>5. CASE r \in S
      BY <1>3, <1>4, <3>3, <3>5 DEF Fresh
    <3>. QED
      BY <3>2, <3>4, <3>5
  <2>3. CASE c1 # c /\ c2 # c
    <3>1. r \in alloc[c1] /\ r \in alloc[c2]
      BY <1>1, <1>4, <2>3 DEF TypeInvariant
    <3>. QED
      BY <1>4, <1>6, <3>1 DEF Mutex
  <2>. QED
    BY <2>1, <2>2, <2>3
<1>. QED
  BY <1>5, <1>6

-------------------------------------------------------------------------

THEOREM NextMutex == TypeInvariant /\ Mutex /\ Next => Mutex'
PROOF
<1>1. ASSUME TypeInvariant /\ Mutex /\ Next
      PROVE  Mutex'
  <2>1. Mutex
    BY <1>1
  <2>1a. TypeInvariant
    BY <1>1
  <2>2. PICK c \in Client, S \in SUBSET Resource :
            Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
    BY <1>1 DEF Next
  <2>3. CASE Request(c,S)
    BY <2>1, <2>2, <2>3, RequestPreservesMutex
  <2>4. CASE Allocate(c,S)
    BY <2>1, <2>1a, <2>2, <2>4, AllocatePreservesMutex
  <2>5. CASE Return(c,S)
    BY <2>1, <2>1a, <2>2, <2>5, ReturnPreservesMutex
  <2>. QED
    BY <2>2, <2>3, <2>4, <2>5
<1>. QED
  BY <1>1

=========================================================================
