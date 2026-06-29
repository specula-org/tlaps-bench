--------------------- MODULE CigaretteSmokers_proof_TypeCorrect ---------------------------

EXTENDS CigaretteSmokers, FiniteSets, FiniteSetTheorems, TLAPS

ASSUME IngredientsFinite == IsFiniteSet(Ingredients)

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

============================================================================
