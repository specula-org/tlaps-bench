(* Contributed by Damien Doligez *)

-------------- MODULE Cantor6_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW f
        PROVE \E A \in SUBSET S :
          \A x \in S :
            f [x] # A
    OBVIOUS
  <1>2. DEFINE A == {x \in S : x \notin f[x]}
  <1>3. A \in SUBSET S
    BY DEF A
  <1>4. \A x \in S : f[x] # A
  PROOF
    <2>1. SUFFICES ASSUME NEW x \in S
          PROVE f[x] # A
      OBVIOUS
    <2>2. x \in A <=> x \notin f[x]
      BY DEF A
    <2>3. CASE x \in f[x]
      <3>1. x \notin A
        BY <2>2, <2>3
      <3>2. QED
        BY <3>1
    <2>4. CASE x \notin f[x]
      <3>1. x \in A
        BY <2>2, <2>4
      <3>2. QED
        BY <3>1
    <2>5. QED
      BY <2>3, <2>4
  <1>5. QED
    BY <1>3, <1>4

===============================================
