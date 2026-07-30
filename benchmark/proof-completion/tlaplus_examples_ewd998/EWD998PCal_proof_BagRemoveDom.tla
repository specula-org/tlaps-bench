---- MODULE EWD998PCal_proof_BagRemoveDom ----
EXTENDS EWD998PCal_proof_BagRemoveDomScaffold
USE NAssumption
LEMMA BagRemoveDom ==
  ASSUME NEW B, NEW x, x \in DOMAIN B
  PROVE  /\ B[x] = 1 => DOMAIN BagRemove(B, x) = DOMAIN B \ {x}
         /\ B[x] # 1 => DOMAIN BagRemove(B, x) = DOMAIN B
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
