-------------------------- MODULE Allocator_NextMutex -----------------------------

(***********************************************************************)
(* Specification of an allocator managing a set of resources:          *)
(* - Clients can request sets of resources whenever all their previous *)
(*   requests have been satisfied.                                     *)
(* - Requests can be partly fulfilled, and resources can be returned   *)
(*   even before the full request has been satisfied. However, clients *)
(*   only have an obligation to return resources after they have       *)
(*   obtained all resources they requested.                            *)
(*                                                                     *)
(* The proofs in this module were written before TLAPS's SMT backend   *)
(* prover was implemented. Much shorter proofs can be obtained using   *)
(* that backend.                                                       *)
(***********************************************************************)

\* EXTENDS FiniteSets, TLC

CONSTANTS
  Client,     \* set of all clients
  Resource    \* set of all resources

\* ASSUME
\*  IsFiniteSet(Resource)

VARIABLES
  unsat,       \* set of all outstanding requests per process
  alloc        \* set of resources allocated to given process

TypeInvariant ==
  /\ unsat \in [Client -> SUBSET Resource]
  /\ alloc \in [Client -> SUBSET Resource]

-------------------------------------------------------------------------

(* Resource are available iff they have not been allocated. *)
available == Resource \ (UNION {alloc[c] : c \in Client})

(* Initially, no resources have been requested or allocated. *)
Init ==
  /\ unsat = [c \in Client |-> {}]
  /\ alloc = [c \in Client |-> {}]

(**********************************************************************)
(* A client c may request a set of resources provided that all of its *)
(* previous requests have been satisfied and that it doesn't hold any *)
(* resources.                                                         *)
(**********************************************************************)
Request(c,S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

(*******************************************************************)
(* Allocation of a set of available resources to a client that     *)
(* requested them (the entire request does not have to be filled). *)
(*******************************************************************)
Allocate(c,S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]

(*******************************************************************)
(* Client c returns a set of resources that it holds. It may do so *)
(* even before its full request has been honored.                  *)
(*******************************************************************)
Return(c,S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
  /\ UNCHANGED unsat

(* The next-state relation. *)
Next ==
  \E c \in Client, S \in SUBSET Resource :
     Request(c,S) \/ Allocate(c,S) \/ Return(c,S)

vars == <<unsat,alloc>>

-------------------------------------------------------------------------


(* The complete high-level specification. *)
SimpleAllocator ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Client: WF_vars(Return(c, alloc[c]))
  /\ \A c \in Client: SF_vars(\E S \in SUBSET Resource: Allocate(c,S))

-------------------------------------------------------------------------

Mutex ==
  \A c1,c2 \in Client : \A r \in Resource :
     r \in alloc[c1] \cap alloc[c2] => c1 = c2

ClientsWillReturn ==
  \A c \in Client : unsat[c]={} ~> alloc[c]={}

ClientsWillObtain ==
  \A c \in Client, r \in Resource : r \in unsat[c] ~> r \in alloc[c]

InfOftenSatisfied ==
  \A c \in Client : []<>(unsat[c] = {})

-------------------------------------------------------------------------

(* Used for symmetry reduction with TLC *)
\* Symmetry == Permutations(Client) \cup Permutations(Resource)

-------------------------------------------------------------------------

(**********************************************************************)
(* The following version states a weaker fairness requirement for the *)
(* clients: resources need be returned only if the entire request has *)
(* been satisfied.                                                    *)
(**********************************************************************)

(*

SimpleAllocator2 ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Client: WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Client: SF_vars(\E S \in SUBSET Resource: Allocate(c,S))

*)

-------------------------------------------------------------------------






-------------------------------------------------------------------------





THEOREM NextMutex == TypeInvariant /\ Mutex /\ Next => Mutex'
<1> SUFFICES ASSUME TypeInvariant, Mutex, Next
             PROVE  Mutex'
    OBVIOUS
<1>1. PICK c \in Client, S \in SUBSET Resource :
         Request(c,S) \/ Allocate(c,S) \/ Return(c,S)
    BY DEF Next
<1>2. alloc \in [Client -> SUBSET Resource]
    BY DEF TypeInvariant
<1>3. CASE Request(c,S)
    BY <1>3 DEF Request, Mutex
<1>4. CASE Return(c,S)
    <2> USE <1>4 DEF Return
    <2>1. \A x \in Client : alloc'[x] = IF x = c THEN alloc[c] \ S ELSE alloc[x]
        BY <1>1, <1>2
    <2>2. \A x \in Client : alloc'[x] \subseteq alloc[x]
        BY <2>1
    <2> SUFFICES ASSUME NEW c1 \in Client, NEW c2 \in Client, NEW r \in Resource,
                        r \in alloc'[c1] \cap alloc'[c2]
                 PROVE  c1 = c2
        BY DEF Mutex
    <2>3. r \in alloc[c1] /\ r \in alloc[c2]
        BY <2>2
    <2> QED
        BY <2>3 DEF Mutex
<1>5. CASE Allocate(c,S)
    <2> USE <1>5 DEF Allocate
    <2>1. \A x \in Client : alloc'[x] = IF x = c THEN alloc[c] \cup S ELSE alloc[x]
        BY <1>1, <1>2
    <2>2. \A x \in Client : S \cap alloc[x] = {}
        BY <1>2 DEF available
    <2> SUFFICES ASSUME NEW c1 \in Client, NEW c2 \in Client, NEW r \in Resource,
                        r \in alloc'[c1] \cap alloc'[c2]
                 PROVE  c1 = c2
        BY DEF Mutex
    <2>3. r \in alloc[c1] \/ (c1 = c /\ r \in S)
        BY <2>1
    <2>4. r \in alloc[c2] \/ (c2 = c /\ r \in S)
        BY <2>1
    <2> QED
        BY <2>2, <2>3, <2>4 DEF Mutex
<1>6. QED
    BY <1>1, <1>3, <1>4, <1>5


(*Allocator.tla
THEOREM SimpleAllocator => InfOftenSatisfied
(** The following do not hold:                          **)
(** THEOREM SimpleAllocator2 => ClientsWillObtain       **)
(** THEOREM SimpleAllocator2 => InfOftenSatisfied       **)

*)

=========================================================================
