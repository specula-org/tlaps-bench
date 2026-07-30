---- MODULE CigaretteSmokers_proof_StopSmokingSmokingSet ----
EXTENDS CigaretteSmokers_proof_StopSmokingSmokingSetScaffold
LEMMA StopSmokingSmokingSet ==
  ASSUME TypeOK, stopSmoking
  PROVE  /\ smokers' \in [Ingredients -> [smoking : BOOLEAN]]
         /\ {r \in Ingredients : smokers'[r].smoking}
              \subseteq {r \in Ingredients : smokers[r].smoking}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
