(* Contributed by Damien Doligez *)

-------------- MODULE Cantor6_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
  <1>1. TAKE S, f
  <1>2. DEFINE A == {x \in S : x \notin f[x]}
  <1>3. A \in SUBSET S
    BY DEF A
  <1>4. \A x \in S : f[x] # A
  PROOF
    <2>1. TAKE x \in S
    <2>2. x \in A <=> x \notin f[x]
      BY DEF A
    <2>3. f[x] # A
      BY <2>2
    <2> QED
      BY <2>3
  <1> QED
    BY <1>3, <1>4

===============================================
