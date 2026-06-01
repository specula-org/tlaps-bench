-------------- MODULE Cantor9_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  ~ \E f : Surj (f, SUBSET (DOMAIN f))
PROOF
  <1>1. ASSUME NEW f, Surj(f, SUBSET (DOMAIN f))
        PROVE FALSE
    PROOF
      <2> DEFINE D == { x \in DOMAIN f : x \notin f[x] }
      <2>1. D \in SUBSET (DOMAIN f) BY DEF D
      <2>2. D \in Range(f) BY <1>1, <2>1 DEF Surj
      <2>3. PICK y \in DOMAIN f : f[y] = D BY <2>2 DEF Range
      <2>4. y \in D <=> y \notin f[y] BY <2>3 DEF D
      <2>5. y \in D <=> y \notin D BY <2>3, <2>4
      <2>6. QED BY <2>5
  <1>2. QED BY <1>1

====
