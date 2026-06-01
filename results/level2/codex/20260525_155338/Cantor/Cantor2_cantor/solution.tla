

-------------- MODULE Cantor2_cantor ------------------
Diagonal(S, f) == {x \in S : x \notin f[x]}

LEMMA DiagonalSubset ==
  \A S :
    \A f \in [S -> SUBSET S] :
      Diagonal(S, f) \in SUBSET S
PROOF
  BY DEF Diagonal

LEMMA DiagonalDiff ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \A x \in S :
        f[x] # Diagonal(S, f)
PROOF
  <1>1. SUFFICES ASSUME NEW S,
                      NEW f \in [S -> SUBSET S],
                      NEW x \in S
               PROVE  f[x] # Diagonal(S, f)
    OBVIOUS
  <1>2. CASE x \in f[x]
    BY <1>1 DEF Diagonal
  <1>3. CASE x \notin f[x]
    BY <1>1 DEF Diagonal
  <1>4. QED BY <1>2, <1>3

THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1>1. SUFFICES ASSUME NEW S,
                      NEW f \in [S -> SUBSET S]
               PROVE  \E A \in SUBSET S :
                        \A x \in S :
                          f[x] # A
    OBVIOUS
  <1>2. Diagonal(S, f) \in SUBSET S
    BY <1>1, DiagonalSubset
  <1>3. \A x \in S : f[x] # Diagonal(S, f)
    BY <1>1, DiagonalDiff
  <1>4. QED BY <1>2, <1>3
===============================================
