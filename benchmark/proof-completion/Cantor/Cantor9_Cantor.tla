---- MODULE Cantor9_Cantor ----
EXTENDS Cantor9_CantorScaffold
THEOREM Cantor ==
  ~ \E f : Surj (f, SUBSET (DOMAIN f))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
