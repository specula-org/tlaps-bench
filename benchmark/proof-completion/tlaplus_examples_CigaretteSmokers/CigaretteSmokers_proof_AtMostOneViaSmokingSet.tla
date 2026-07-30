---- MODULE CigaretteSmokers_proof_AtMostOneViaSmokingSet ----
EXTENDS CigaretteSmokers_proof_AtMostOneViaSmokingSetScaffold
LEMMA AtMostOneViaSmokingSet == AtMostOne <=> Cardinality(SmokingSet) <= 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
