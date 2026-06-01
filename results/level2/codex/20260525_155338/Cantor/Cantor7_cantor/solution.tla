

-------------- MODULE Cantor7_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW f
                PROVE  \E A \in SUBSET S :
                         \A x \in S :
                           f [x] # A
    OBVIOUS
  <1>2. DEFINE A == {x \in S : x \notin f[x]}
  <1>3. A \in SUBSET S
    BY DEF A
  <1>4. \A x \in S : f[x] # A
    <2>1. SUFFICES ASSUME NEW x \in S
                  PROVE  f[x] # A
      OBVIOUS
    <2>2. ASSUME f[x] = A
          PROVE  FALSE
      <3>1. x \in A <=> x \notin f[x]
        BY <2>1 DEF A
      <3>2. x \in A <=> x \in f[x]
        BY <2>2
      <3>. QED
        BY <3>1, <3>2
    <2>. QED
      BY <2>2
  <1>. QED
    BY <1>3, <1>4
===============================================
