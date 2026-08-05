--------------------- MODULE SchedulingAllocator_proof_TypeCorrectDefs ---------------------

EXTENDS SchedulingAllocator, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

ASSUME ClientsFinite == IsFiniteSet(Clients)

============================================================================
