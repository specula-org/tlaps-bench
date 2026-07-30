---- MODULE CigaretteSmokers_proof_OffersFact ----
EXTENDS CigaretteSmokers_proof_OffersFactScaffold
LEMMA OffersFact ==
  /\ Offers \subseteq SUBSET Ingredients
  /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
