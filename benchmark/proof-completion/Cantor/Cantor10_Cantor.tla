---- MODULE Cantor10_Cantor ----
EXTENDS Cantor10_CantorScaffold
THEOREM Cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
