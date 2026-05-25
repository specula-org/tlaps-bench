(* Contributed by Stephan Merz *)

-------------- MODULE Cantor4_cantor ------------------
THEOREM cantor ==
 \A S :
   \A f \in [S -> SUBSET S] :
     \E A \in SUBSET S :
       \A x \in S :
         f [x] # A
PROOF
<1> SUFFICES ASSUME NEW S, NEW f \in [S -> SUBSET S]
             PROVE \E A \in SUBSET S : \A x \in S : f[x] # A
  OBVIOUS
<1> DEFINE A == {x \in S : x \notin f[x]}
<1>1. A \in SUBSET S
  OBVIOUS
<1>2. \A x \in S : f[x] # A
  BY DEF A
<1>3. QED
  BY <1>1, <1>2
===============================================
