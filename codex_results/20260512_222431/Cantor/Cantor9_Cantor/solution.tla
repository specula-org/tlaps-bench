-------------- MODULE Cantor9_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  ~ \E f : Surj (f, SUBSET (DOMAIN f))
PROOF
<1>1. SUFFICES ASSUME NEW f, Surj (f, SUBSET (DOMAIN f))
      PROVE FALSE
  OBVIOUS
<1>2. DEFINE D == {x \in DOMAIN f : x \notin f[x]}
<1>3. D \in SUBSET (DOMAIN f)
  OBVIOUS
<1>4. D \in Range(f)
  BY <1>1, <1>3 DEF Surj
<1>5. \E y \in DOMAIN f : f[y] = D
  BY <1>4 DEF Range
<1>6. PICK y \in DOMAIN f : f[y] = D
  BY <1>5
<1>7. y \in D <=> y \notin f[y]
  BY <1>6 DEF D
<1>8. y \in D <=> y \notin D
  BY <1>6, <1>7
<1>9. FALSE
  BY <1>8
<1>10. QED
  BY <1>1, <1>9

====
