---- MODULE CigaretteSmokers_proof_SmokingSetFinite ----
EXTENDS CigaretteSmokers_proof_SmokingSetFiniteScaffold
LEMMA SmokingSetFinite ==
  ASSUME TypeOK
  PROVE  /\ IsFiniteSet(SmokingSet)
         /\ Cardinality(SmokingSet) \in Nat
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
