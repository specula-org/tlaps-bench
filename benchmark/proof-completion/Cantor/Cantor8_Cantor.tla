---- MODULE Cantor8_Cantor ----
EXTENDS Cantor8_CantorScaffold
THEOREM Cantor ==
  \A S : ~ \E f \in [S -> SUBSET S] : Surj (f, SUBSET S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
