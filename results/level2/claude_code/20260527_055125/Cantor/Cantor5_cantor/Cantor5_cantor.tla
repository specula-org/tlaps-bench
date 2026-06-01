

-------------- MODULE Cantor5_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
<1>1. TAKE S, f
<1> DEFINE A == {x \in S : x \notin f[x]}
<1>2. A \in SUBSET S
  BY DEF A
<1>3. \A x \in S : f[x] # A
  <2>1. TAKE x \in S
  <2>2. QED
    BY DEF A
<1>4. QED
  BY <1>2, <1>3
===============================================
