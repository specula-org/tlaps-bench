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

LEMMA UnionSubsetResource ==
  ASSUME NEW A \in SUBSET Resource,
         NEW B \in SUBSET Resource
  PROVE  A \cup B \in SUBSET Resource
PROOF OBVIOUS

LEMMA DifferenceSubsetResource ==
  ASSUME NEW A \in SUBSET Resource,
         NEW B
  PROVE  A \ B \in SUBSET Resource
PROOF OBVIOUS

LEMMA UpdateType ==
  ASSUME NEW f \in [Client -> SUBSET Resource],
         NEW c \in Client,
         NEW A \in SUBSET Resource
  PROVE  [f EXCEPT ![c] = A] \in [Client -> SUBSET Resource]
PROOF OBVIOUS

LEMMA RequestTypeInvariant ==
  ASSUME TypeInvariant,
         NEW c \in Client,
         NEW S \in SUBSET Resource,
         Request(c,S)
  PROVE  TypeInvariant'
PROOF
  <1>1. unsat' \in [Client -> SUBSET Resource]
    BY UpdateType DEF TypeInvariant, Request
  <1>2. alloc' \in [Client -> SUBSET Resource]
    BY DEF TypeInvariant, Request
  <1>. QED BY <1>1, <1>2 DEF TypeInvariant

LEMMA AllocateTypeInvariant ==
  ASSUME TypeInvariant,
         NEW c \in Client,
         NEW S \in SUBSET Resource,
         Allocate(c,S)
  PROVE  TypeInvariant'
PROOF
  <1>1. alloc[c] \in SUBSET Resource
    BY DEF TypeInvariant
  <1>2. unsat[c] \in SUBSET Resource
    BY DEF TypeInvariant
  <1>3. alloc[c] \cup S \in SUBSET Resource
    BY <1>1, UnionSubsetResource
  <1>4. unsat[c] \ S \in SUBSET Resource
    BY <1>2, DifferenceSubsetResource
  <1>5. alloc' \in [Client -> SUBSET Resource]
    BY <1>3, UpdateType DEF TypeInvariant, Allocate
  <1>6. unsat' \in [Client -> SUBSET Resource]
    BY <1>4, UpdateType DEF TypeInvariant, Allocate
  <1>. QED BY <1>5, <1>6 DEF TypeInvariant

LEMMA ReturnTypeInvariant ==
  ASSUME TypeInvariant,
         NEW c \in Client,
         NEW S \in SUBSET Resource,
         Return(c,S)
  PROVE  TypeInvariant'
PROOF
  <1>1. alloc[c] \in SUBSET Resource
    BY DEF TypeInvariant
  <1>2. alloc[c] \ S \in SUBSET Resource
    BY <1>1, DifferenceSubsetResource
  <1>3. alloc' \in [Client -> SUBSET Resource]
    BY <1>2, UpdateType DEF TypeInvariant, Return
  <1>4. unsat' \in [Client -> SUBSET Resource]
    BY DEF TypeInvariant, Return
  <1>. QED BY <1>3, <1>4 DEF TypeInvariant

-------------------------------------------------------------------------

-------------------------------------------------------------------------

THEOREM NextTypeInvariant == TypeInvariant /\ Next => TypeInvariant'
PROOF
  <1>1. ASSUME TypeInvariant /\ Next
         PROVE  TypeInvariant'
    <2>1. TypeInvariant
      BY <1>1
    <2>2. Next
      BY <1>1
    <2>3. PICK c \in Client, S \in SUBSET Resource :
              Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
      BY <2>2 DEF Next
    <2>4. ASSUME Request(c,S)
           PROVE  TypeInvariant'
      BY <2>1, <2>3, <2>4, RequestTypeInvariant
    <2>5. ASSUME Allocate(c,S)
           PROVE  TypeInvariant'
      BY <2>1, <2>3, <2>5, AllocateTypeInvariant
    <2>6. ASSUME Return(c,S)
           PROVE  TypeInvariant'
      BY <2>1, <2>3, <2>6, ReturnTypeInvariant
    <2>. QED BY <2>3, <2>4, <2>5, <2>6
  <1>. QED BY <1>1

-------------------------------------------------------------------------

=========================================================================
