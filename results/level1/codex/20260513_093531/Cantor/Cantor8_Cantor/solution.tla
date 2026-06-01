-------------- MODULE Cantor8_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  \A S : ~ \E f \in [S -> SUBSET S] : Surj (f, SUBSET S)
PROOF
  <1>1. SUFFICES ASSUME NEW S
                 PROVE  ~ \E f \in [S -> SUBSET S] : Surj(f, SUBSET S)
    OBVIOUS
  <1>2. ASSUME \E f \in [S -> SUBSET S] : Surj(f, SUBSET S)
        PROVE  FALSE
    <2>1. PICK f \in [S -> SUBSET S] : Surj(f, SUBSET S)
      BY <1>2
    <2>2. DEFINE D == {x \in S : x \notin f[x]}
    <2>3. D \in SUBSET S
      BY DEF D
    <2>4. D \in Range(f)
      BY <2>1, <2>3 DEF Surj
    <2>5. PICK y \in DOMAIN f : D = f[y]
      BY <2>4 DEF Range
    <2>6. y \in S
      BY <2>1, <2>5
    <2>7. y \in D <=> y \notin f[y]
      BY <2>6 DEF D
    <2>8. y \in f[y] <=> y \in D
      BY <2>5
    <2>9. FALSE
      BY <2>7, <2>8
    <2> QED
      BY <2>9
  <1> QED
    BY <1>1, <1>2

====
