(* Contributed by Leslie Lamport *)

-------------- MODULE Cantor3_cantor ------------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1>1. TAKE S
  <1>2. TAKE f \in [S -> SUBSET S]
  <1>3. DEFINE A == {x \in S : x \notin f[x]}
  <1>4. A \in SUBSET S
    BY DEF A
  <1>5. \A x \in S : f[x] # A
  PROOF
    <2>1. TAKE x \in S
    <2>2. x \in A <=> x \notin f[x]
      BY <2>1 DEF A
    <2>3. f[x] # A
    PROOF
      <3>1. SUFFICES ASSUME f[x] = A PROVE FALSE
        OBVIOUS
      <3>2. x \in f[x] <=> x \in A
        BY <3>1
      <3>3. x \in f[x] <=> x \notin f[x]
        BY <2>2, <3>2
      <3>4. QED
        BY <3>3
    <2>4. QED
      BY <2>3
  <1>6. QED
    BY <1>4, <1>5

===============================================
