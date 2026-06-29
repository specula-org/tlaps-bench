----------------------- MODULE SimpleAllocator_proof_Mutex -----------------------
(***************************************************************************)
(* TLAPS proofs of two safety properties of the SimpleAllocator spec:      *)
(*                                                                         *)
(*   SimpleAllocator => []TypeInvariant                                    *)
(*   SimpleAllocator => []ResourceMutex                                    *)
(*                                                                         *)
(* TypeInvariant is directly inductive.  ResourceMutex needs TypeInvariant *)
(* together with the simple observation that an Allocate(c, S) action      *)
(* takes S from the `available` resources, so S is disjoint from every     *)
(* alloc[c'] for c' # c.                                                  *)
(***************************************************************************)
EXTENDS SimpleAllocator, TLAPS

(***************************************************************************)
(*                       SimpleAllocator => []TypeInvariant                *)
(***************************************************************************)

THEOREM TypeCorrect == SimpleAllocator => []TypeInvariant
PROOF OMITTED

(***************************************************************************)
(*                       SimpleAllocator => []ResourceMutex                *)
(***************************************************************************)

(***************************************************************************)
(* The combined inductive invariant.  We need TypeInvariant in scope to   *)
(* type-check alloc[c]; ResourceMutex on its own is preserved given       *)
(* TypeInvariant.                                                         *)
(***************************************************************************)
Inv == TypeInvariant /\ ResourceMutex

THEOREM Mutex == SimpleAllocator => []ResourceMutex
PROOF OBVIOUS

============================================================================
