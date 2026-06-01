(* Contributed by Damien Doligez *)

-------------- MODULE Cantor5_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
<1> TAKE S, f
<1> DEFINE A == {x \in S : x \notin f[x]}
<1>1. A \in SUBSET S
  BY DEF A
<1>2. ASSUME NEW x \in S
       PROVE  f[x] # A
  <2>1. x \in A <=> x \notin f[x]
    BY DEF A
  <2>. QED BY <2>1
<1>. QED BY <1>1, <1>2

===============================================
