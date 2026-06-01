-------------- MODULE Cantor9_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

Diagonal(f) == { x \in DOMAIN f : x \notin f[x] }

LEMMA DiagonalSubset ==
  \A f : Diagonal(f) \in SUBSET DOMAIN f
PROOF
  <1>1. ASSUME NEW f
        PROVE  Diagonal(f) \in SUBSET DOMAIN f
    BY DEF Diagonal
  <1>. QED BY <1>1

LEMMA DiagonalNotInRange ==
  \A f : Diagonal(f) \notin Range(f)
PROOF
  <1>. SUFFICES ASSUME NEW f, Diagonal(f) \in Range(f)
                PROVE  FALSE
    OBVIOUS
  <1>1. PICK y \in DOMAIN f : f[y] = Diagonal(f)
    BY DEF Range
  <1>2. y \in Diagonal(f) => y \notin Diagonal(f)
    BY <1>1 DEF Diagonal
  <1>3. y \notin Diagonal(f) => y \in Diagonal(f)
    BY <1>1 DEF Diagonal
  <1>. QED BY <1>2, <1>3

THEOREM Cantor ==
  ~ \E f : Surj (f, SUBSET (DOMAIN f))
PROOF
  <1>. SUFFICES ASSUME NEW f, Surj(f, SUBSET (DOMAIN f))
                PROVE  FALSE
    OBVIOUS
  <1>1. Diagonal(f) \in SUBSET (DOMAIN f)
    BY DiagonalSubset
  <1>2. Diagonal(f) \in Range(f)
    BY <1>1 DEF Surj
  <1>3. Diagonal(f) \notin Range(f)
    BY DiagonalNotInRange
  <1>. QED BY <1>2, <1>3

====
