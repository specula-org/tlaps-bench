--------------------- MODULE SchedulingAllocator_proof_MutexDefs ---------------------

EXTENDS SchedulingAllocator, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

ASSUME ClientsFinite == IsFiniteSet(Clients)

============================================================================
