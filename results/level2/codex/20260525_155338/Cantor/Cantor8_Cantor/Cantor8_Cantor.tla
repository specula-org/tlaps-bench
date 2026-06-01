-------------- MODULE Cantor8_Cantor --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

Diag (S, f) == { x \in S : x \notin f[x] }

LEMMA DiagSubset ==
  \A S, f : Diag(S, f) \in SUBSET S
PROOF BY DEF Diag

THEOREM Cantor ==
  \A S : ~ \E f \in [S -> SUBSET S] : Surj (f, SUBSET S)
PROOF
<1>1. SUFFICES ASSUME NEW S
                  PROVE  ~ \E f \in [S -> SUBSET S] : Surj(f, SUBSET S)
  OBVIOUS
<1>2. SUFFICES ASSUME NEW f \in [S -> SUBSET S],
                         Surj(f, SUBSET S)
                  PROVE  FALSE
  OBVIOUS
<1>3. Diag(S, f) \in SUBSET S
  BY DiagSubset
<1>4. Diag(S, f) \in Range(f)
  BY <1>2, <1>3 DEF Surj
<1>5. PICK s \in DOMAIN f : Diag(S, f) = f[s]
  BY <1>4 DEF Range
<1>6. s \in S
  BY <1>2, <1>5
<1>7. s \in Diag(S, f) <=> s \notin f[s]
  BY <1>6 DEF Diag
<1>8. s \in f[s] <=> s \in Diag(S, f)
  BY <1>5
<1>9. QED
  BY <1>7, <1>8

====
