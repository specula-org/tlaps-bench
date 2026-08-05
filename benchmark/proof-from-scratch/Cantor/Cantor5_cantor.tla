---- MODULE Cantor5_cantor ----
EXTENDS Cantor5_cantorDefs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
