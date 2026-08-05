---- MODULE Cantor2_cantor ----
EXTENDS Cantor2_cantorDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
