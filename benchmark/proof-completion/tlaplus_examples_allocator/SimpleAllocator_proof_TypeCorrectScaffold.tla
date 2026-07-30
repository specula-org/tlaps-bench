----------------------- MODULE SimpleAllocator_proof_TypeCorrectScaffold -----------------------
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

=============================================================================
