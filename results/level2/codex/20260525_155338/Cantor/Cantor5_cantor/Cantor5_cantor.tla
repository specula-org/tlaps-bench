

-------------- MODULE Cantor5_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
<1> TAKE S, f
<1> DEFINE D == {x \in S : x \notin f[x]}
  <1>1. D \in SUBSET S
    OBVIOUS
  <1>2. \A x \in S : f[x] # D
  PROOF
    <2>1. ASSUME NEW x \in S
          PROVE  f[x] # D
    PROOF
      <3>1. SUFFICES ASSUME f[x] = D
                    PROVE  FALSE
        OBVIOUS
      <3>2. x \in D <=> x \notin D
        BY <2>1, <3>1 DEF D
      <3>. QED
        BY <3>2
    <2>. QED BY <2>1
  <1>3. QED
    BY <1>1, <1>2
===============================================
