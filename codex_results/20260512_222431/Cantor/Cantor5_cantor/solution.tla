(* Contributed by Damien Doligez *)

-------------- MODULE Cantor5_cantor ------------------
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
  <1> DEFINE A == {x \in S : x \notin f[x]}
  <1>2. A \in SUBSET S
    OBVIOUS
  <1>3. \A x \in S : f[x] # A
    PROOF
      <2>1. SUFFICES ASSUME NEW x \in S
                     PROVE  f[x] # A
        OBVIOUS
      <2>2. SUFFICES ASSUME f[x] = A
                     PROVE  FALSE
        OBVIOUS
      <2>3. x \in A <=> x \notin f[x]
        BY DEF A
      <2>4. x \in A <=> x \notin A
        BY <2>2, <2>3
      <2>5. FALSE
        BY <2>4
      <2>6. QED
        BY <2>5
  <1>4. QED
    BY <1>2, <1>3

===============================================
