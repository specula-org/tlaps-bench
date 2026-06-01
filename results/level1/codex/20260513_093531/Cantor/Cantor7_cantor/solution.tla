(* Contributed by Damien Doligez *)

-------------- MODULE Cantor7_cantor ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
  <1>1. ASSUME NEW S, NEW f
        PROVE \E A \in SUBSET S :
                \A x \in S :
                  f [x] # A
    <2>1. DEFINE D == { x \in S : x \notin f[x] }
    <2>2. D \in SUBSET S
      OBVIOUS
    <2>3. \A x \in S : f[x] # D
      <3>1. TAKE x \in S
      <3>2. ASSUME f[x] = D
            PROVE FALSE
        <4>1. x \in D <=> x \notin f[x]
          BY <3>1 DEF D
        <4>2. x \in D <=> x \notin D
          BY <3>2, <4>1
        <4>3. QED BY <4>2
      <3>3. QED BY <3>2
    <2>4. QED BY <2>2, <2>3
  <1>2. QED BY <1>1
===============================================
