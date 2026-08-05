--------------------- MODULE AllocatorImplementation_proof_TypeCorrectDefs -----------------

EXTENDS AllocatorImplementation, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

ASSUME ClientsFinite == IsFiniteSet(Clients)

============================================================================
