-------------- MODULE Cantor9_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  ~ \E f : Surj (f, SUBSET (DOMAIN f))
PROOF
<1>1. SUFFICES ASSUME NEW f, Surj (f, SUBSET (DOMAIN f))
               PROVE  FALSE
  OBVIOUS
<1> DEFINE C == { x \in DOMAIN f : x \notin f[x] }
<1>0. SUBSET (DOMAIN f) \subseteq Range (f)
  BY <1>1 DEF Surj
<1>2. C \in SUBSET (DOMAIN f)
  OBVIOUS
<1>3. C \in Range (f)
  BY <1>0, <1>2
<1>4. PICK y \in DOMAIN f : f[y] = C
  BY <1>3 DEF Range
<1>5. y \in C <=> y \notin f[y]
  OBVIOUS
<1>6. QED
  BY <1>4, <1>5

====
