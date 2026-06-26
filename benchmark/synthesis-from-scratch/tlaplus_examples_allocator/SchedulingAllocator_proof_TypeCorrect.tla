--------------------- MODULE SchedulingAllocator_proof_TypeCorrect ---------------------

EXTENDS SchedulingAllocator, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

ASSUME ClientsFinite == IsFiniteSet(Clients)

THEOREM TypeCorrect == Allocator => []TypeInvariant
PROOF OBVIOUS

============================================================================
