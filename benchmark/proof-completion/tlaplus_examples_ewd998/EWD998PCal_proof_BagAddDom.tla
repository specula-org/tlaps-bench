---- MODULE EWD998PCal_proof_BagAddDom ----
EXTENDS EWD998PCal_proof_BagAddDomScaffold
USE NAssumption
LEMMA BagAddDom ==
  ASSUME NEW B, NEW x
  PROVE  DOMAIN BagAdd(B, x) = DOMAIN B \cup {x}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
