(* Contributed by Leslie Lamport *)

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
                PROVE \E A \in SUBSET S :
                        \A x \in S : f[x] # A
    OBVIOUS
  <1>2. DEFINE A == {x \in S : x \notin f[x]}
  <1>3. A \in SUBSET S
    OBVIOUS
  <1>4. \A x \in S : f[x] # A
  PROOF
    <2>1. TAKE x \in S
    <2>2. ASSUME f[x] = A
          PROVE FALSE
    PROOF
      <3>1. x \in f[x] => x \notin f[x]
        BY <2>1, <2>2 DEF A
      <3>2. x \notin f[x] => x \in f[x]
        BY <2>1, <2>2 DEF A
      <3>3. QED
        BY <3>1, <3>2
    <2>3. QED
      BY <2>2
  <1>5. QED
    BY <1>3, <1>4

===============================================
