---- MODULE CigaretteSmokers_proof_UniqueComplement2 ----
EXTENDS CigaretteSmokers_proof_UniqueComplement2Scaffold
LEMMA UniqueComplement2 ==
  ASSUME TypeOK, dealer \in Offers
  PROVE  Cardinality({r \in Ingredients : {r} \cup dealer = Ingredients}) = 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
