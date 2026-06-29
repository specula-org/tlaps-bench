--------------------- MODULE SchedulingAllocator_proof_Mutex ---------------------

EXTENDS SchedulingAllocator, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

ASSUME ClientsFinite == IsFiniteSet(Clients)

THEOREM Mutex == Allocator => []ResourceMutex
PROOF OBVIOUS

============================================================================
