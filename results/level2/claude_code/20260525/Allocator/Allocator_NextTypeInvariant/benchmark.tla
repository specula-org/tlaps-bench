-------------------------- MODULE Allocator_NextTypeInvariant -----------------------------

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





THEOREM NextTypeInvariant == TypeInvariant /\ Next => TypeInvariant'
PROOF OBVIOUS

-------------------------------------------------------------------------







(*Allocator.tla
THEOREM SimpleAllocator => InfOftenSatisfied
(** The following do not hold:                          **)
(** THEOREM SimpleAllocator2 => ClientsWillObtain       **)
(** THEOREM SimpleAllocator2 => InfOftenSatisfied       **)

*)

=========================================================================
