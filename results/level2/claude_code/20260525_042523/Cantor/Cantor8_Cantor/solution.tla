-------------- MODULE Cantor8_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  \A S : ~ \E f \in [S -> SUBSET S] : Surj (f, SUBSET S)
PROOF
  <1>1. ASSUME NEW S,
               NEW f \in [S -> SUBSET S],
               Surj (f, SUBSET S)
        PROVE  FALSE
    <2> DEFINE D == { x \in S : x \notin f[x] }
    <2>1. D \in SUBSET S
      OBVIOUS
    <2>2. D \in Range (f)
      BY <1>1, <2>1 DEF Surj
    <2>3. PICK y \in S : f[y] = D
      BY <2>2 DEF Range
    <2>4. y \in D <=> y \notin f[y]
      OBVIOUS
    <2>5. QED
      BY <2>3, <2>4
  <1>2. QED
    BY <1>1

====
