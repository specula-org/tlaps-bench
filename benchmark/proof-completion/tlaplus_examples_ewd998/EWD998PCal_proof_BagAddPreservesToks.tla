---- MODULE EWD998PCal_proof_BagAddPreservesToks ----
EXTENDS EWD998PCal_proof_BagAddPreservesToksScaffold
USE NAssumption
LEMMA BagAddPreservesToks ==
  ASSUME NEW B, NEW x, x.type # "tok"
  PROVE  /\ \A t : t.type = "tok" /\ t \in DOMAIN B
                  => /\ t \in DOMAIN BagAdd(B, x)
                     /\ BagAdd(B, x)[t] = B[t]
         /\ \A t : t.type = "tok" /\ t \in DOMAIN BagAdd(B, x)
                  => t \in DOMAIN B
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
