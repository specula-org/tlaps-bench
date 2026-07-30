---- MODULE CigaretteSmokers_proof_StartSmokingSmokingSet ----
EXTENDS CigaretteSmokers_proof_StartSmokingSmokingSetScaffold
LEMMA StartSmokingSmokingSet ==
  ASSUME TypeOK, startSmoking
  PROVE  /\ smokers' \in [Ingredients -> [smoking : BOOLEAN]]
         /\ {r \in Ingredients : smokers'[r].smoking}
              = {r \in Ingredients : {r} \cup dealer = Ingredients}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
