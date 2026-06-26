--------------------- MODULE CigaretteSmokers_proof_AtMostOneCorrect ---------------------------

EXTENDS CigaretteSmokers, FiniteSets, FiniteSetTheorems, TLAPS

ASSUME IngredientsFinite == IsFiniteSet(Ingredients)

THEOREM AtMostOneCorrect == Spec => []AtMostOne
PROOF OBVIOUS
============================================================================
