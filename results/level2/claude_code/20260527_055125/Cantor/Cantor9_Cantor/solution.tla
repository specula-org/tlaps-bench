-------------- MODULE Cantor9_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  ~ \E f : Surj (f, SUBSET (DOMAIN f))
PROOF
  <1> SUFFICES ASSUME NEW f, Surj(f, SUBSET (DOMAIN f))
               PROVE  FALSE
    OBVIOUS
  <1> DEFINE T == { x \in DOMAIN f : x \notin f[x] }
  <1>1. T \in SUBSET (DOMAIN f)
    BY DEF T
  <1>2. T \in Range (f)
    BY <1>1 DEF Surj
  <1>3. PICK y \in DOMAIN f : f[y] = T
    BY <1>2 DEF Range
  <1>4. QED
    BY <1>3 DEF T

====
