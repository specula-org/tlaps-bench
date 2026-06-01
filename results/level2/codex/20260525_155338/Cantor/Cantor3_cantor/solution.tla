

-------------- MODULE Cantor3_cantor ------------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1>1. SUFFICES ASSUME NEW S,
                         NEW f \in [S -> SUBSET S]
                  PROVE  \E A \in SUBSET S :
                           \A x \in S :
                             f[x] # A
    OBVIOUS
  <1>2. DEFINE A == {x \in S : x \notin f[x]}
  <1>3. A \in SUBSET S
    BY DEF A
  <1>4. \A x \in S : f[x] # A
    <2>1. SUFFICES ASSUME NEW x \in S
                    PROVE  f[x] # A
      OBVIOUS
    <2>2. x \in A <=> x \notin f[x]
      BY DEF A
    <2>3. f[x] = A => FALSE
      <3>1. ASSUME f[x] = A
              PROVE FALSE
        <4>1. x \in A <=> x \in f[x]
          BY <3>1
        <4>2. x \in f[x] <=> x \notin f[x]
          BY <2>2, <4>1
        <4>3. QED
          BY <4>2
      <3>2. QED
        BY <3>1
    <2>4. QED
      BY <2>3
  <1>5. QED
    BY <1>3, <1>4
===============================================
