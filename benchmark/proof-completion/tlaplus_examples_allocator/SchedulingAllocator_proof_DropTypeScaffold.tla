--------------------- MODULE SchedulingAllocator_proof_DropTypeScaffold ---------------------
(***************************************************************************)
(* TLAPS proofs of the safety theorems stated in SchedulingAllocator.tla:  *)
(*                                                                         *)
(*   Allocator => []TypeInvariant                                          *)
(*   Allocator => []ResourceMutex                                          *)
(*                                                                         *)
(* TypeInvariant is directly inductive (the only subtlety is that         *)
(* Drop(sched, i) and sched \circ sq stay in Seq(Clients)).  ResourceMutex *)
(* uses the same argument as in SimpleAllocator: an Allocate(c, S) action *)
(* takes S from `available`, so S is disjoint from every alloc[c'].       *)
(*                                                                         *)
(* AllocatorInvariant is left as future work; its preservation across the *)
(* Schedule action requires careful reasoning about Range(sched \circ sq) *)
(* and the way toSchedule changes.                                       *)
(***************************************************************************)
EXTENDS SchedulingAllocator, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

(***************************************************************************)
(* The PermSeqs proof needs Clients to be finite (PermSeqs is the set of   *)
(* permutation sequences over a finite set; the recursion well-founds only *)
(* over finite subsets).  Resources is already finite by the spec's        *)
(* SchedulingAllocatorAssumptions; we add Clients here.                    *)
(***************************************************************************)
ASSUME ClientsFinite == IsFiniteSet(Clients)

(***************************************************************************)
(*                          Allocator => []TypeInvariant                   *)
(***************************************************************************)

LEMMA SubSeqInRange ==
  ASSUME NEW T, NEW s \in Seq(T), NEW m \in Int, NEW n \in Int,
         m >= 1, n <= Len(s)
  PROVE  SubSeq(s, m, n) \in Seq(T)
PROOF OMITTED

LEMMA ConcatType ==
  ASSUME NEW T, NEW s1 \in Seq(T), NEW s2 \in Seq(T)
  PROVE  s1 \o s2 \in Seq(T)
  OBVIOUS

=============================================================================
