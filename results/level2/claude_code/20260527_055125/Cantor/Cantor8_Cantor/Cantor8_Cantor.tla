-------------- MODULE Cantor8_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

LEMMA NoSurjection ==
  ASSUME NEW S, NEW f \in [S -> SUBSET S], Surj(f, SUBSET S)
  PROVE  FALSE
PROOF
<1>1. SUBSET S \subseteq Range(f)
  BY DEF Surj
<1> DEFINE D == { x \in S : x \notin f[x] }
<1>2. D \in SUBSET S
  BY DEF D
<1>3. D \in Range(f)
  BY <1>1, <1>2
<1>4. PICK y \in DOMAIN f : f[y] = D
  BY <1>3 DEF Range
<1>5. y \in S
  BY <1>4
<1>6. QED
  BY <1>4, <1>5 DEF D

THEOREM Cantor ==
  \A S : ~ \E f \in [S -> SUBSET S] : Surj (f, SUBSET S)
PROOF
<1>1. TAKE S
<1>2. QED
  BY NoSurjection

====
