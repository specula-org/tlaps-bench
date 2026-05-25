(* Contributed by Damien Doligez *)

-------------- MODULE Cantor5_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
  <1> TAKE S, f
  <1> DEFINE D == {z \in S : z \notin f[z]}
  <1>1. D \in SUBSET S
    OBVIOUS
  <1>2. \A x \in S : f[x] # D
    <2> TAKE x \in S
    <2>1. SUFFICES ASSUME f[x] = D
                   PROVE FALSE
      OBVIOUS
    <2>2. x \in D <=> x \notin f[x]
      OBVIOUS
    <2>3. QED
      BY <2>1, <2>2
  <1>3. QED
    <2> WITNESS D \in SUBSET S
    <2> QED
      BY <1>2
===============================================
