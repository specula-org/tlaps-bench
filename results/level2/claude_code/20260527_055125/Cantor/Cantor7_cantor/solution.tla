

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
  BY DEF A
<1>3. \A x \in S : f[x] # A
  <2>1. ASSUME NEW x \in S
        PROVE f[x] # A
    <3>1. x \in A <=> x \notin f[x]
      BY DEF A
    <3>2. QED
      BY <3>1
  <2>2. QED
    BY <2>1
<1>4. QED
  BY <1>2, <1>3
===============================================
