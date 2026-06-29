(* Contributed by Stephan Merz *)

-------------- MODULE Cantor4_cantor ------------------
THEOREM cantor ==
 \A S :
   \A f \in [S -> SUBSET S] :
     \E A \in SUBSET S :
       \A x \in S :
         f [x] # A
PROOF OBVIOUS
===============================================
