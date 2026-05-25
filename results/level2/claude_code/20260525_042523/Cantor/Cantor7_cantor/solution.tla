(* Contributed by Damien Doligez *)

-------------- MODULE Cantor7_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
<1>1. TAKE S, f
<1> DEFINE A == {x \in S : x \notin f[x]}
<1>2. A \in SUBSET S
  OBVIOUS
<1>3. WITNESS A \in SUBSET S
<1>4. TAKE x \in S
<1>5. SUFFICES ASSUME f[x] = A
                PROVE  FALSE
  OBVIOUS
<1>6. x \in A <=> x \notin f[x]
  BY DEF A
<1>7. QED
  BY <1>5, <1>6
===============================================
