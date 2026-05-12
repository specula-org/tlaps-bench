(* Contributed by Damien Doligez *)

-------------- MODULE Cantor5_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF OBVIOUS

===============================================