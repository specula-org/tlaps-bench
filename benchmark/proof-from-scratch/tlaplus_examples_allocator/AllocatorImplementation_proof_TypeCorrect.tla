--------------------- MODULE AllocatorImplementation_proof_TypeCorrect -----------------

EXTENDS AllocatorImplementation, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

ASSUME ClientsFinite == IsFiniteSet(Clients)

THEOREM TypeCorrect == Specification => []TypeInvariant
PROOF OBVIOUS

============================================================================
