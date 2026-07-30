---- MODULE EWD998PCal_proof_BagRemovePreservesToks ----
EXTENDS EWD998PCal_proof_BagRemovePreservesToksScaffold
USE NAssumption
LEMMA BagRemovePreservesToks ==
  ASSUME NEW B, NEW x, x.type # "tok"
  PROVE  /\ \A t : t.type = "tok" /\ t \in DOMAIN B
                  => /\ t \in DOMAIN BagRemove(B, x)
                     /\ BagRemove(B, x)[t] = B[t]
         /\ \A t : t.type = "tok" /\ t \in DOMAIN BagRemove(B, x)
                  => t \in DOMAIN B
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
