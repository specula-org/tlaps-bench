-------------- MODULE Cantor8_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  \A S : ~ \E f \in [S -> SUBSET S] : Surj (f, SUBSET S)
PROOF
  <1>1. SUFFICES ASSUME NEW S,
                       NEW f \in [S -> SUBSET S],
                       Surj(f, SUBSET S)
                PROVE  FALSE
    BY DEF Surj
  <1>2. DEFINE D == { x \in S : x \notin f[x] }
  <1>3. D \in SUBSET S
    OBVIOUS
  <1>4. PICK y \in DOMAIN f : f[y] = D
    BY <1>1, <1>3 DEF Surj, Range
  <1>5. y \in S
    BY <1>1, <1>4
  <1>6. y \in f[y] <=> y \notin f[y]
    BY <1>4, <1>5 DEF D
  <1>7. FALSE
    BY <1>6
  <1> QED
    BY <1>7

====
