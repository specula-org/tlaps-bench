

-------------- MODULE Cantor6_cantor ------------------
Diagonal(S, f) == {x \in S : x \notin f[x]}

LEMMA DiagonalInSubset ==
  \A S, f : Diagonal(S, f) \in SUBSET S
PROOF
  BY DEF Diagonal

LEMMA DiagonalDiffers ==
  \A S, f, x :
    x \in S => f[x] # Diagonal(S, f)
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW f, NEW x,
                       x \in S
                PROVE  f[x] # Diagonal(S, f)
    OBVIOUS
  <1>2. x \in Diagonal(S, f) <=> x \notin f[x]
    BY <1>1 DEF Diagonal
  <1>3. f[x] # Diagonal(S, f)
  PROOF
    <2>1. ASSUME f[x] = Diagonal(S, f)
            PROVE  FALSE
    PROOF
      <3>1. x \in f[x] <=> x \in Diagonal(S, f)
        BY <2>1
      <3>2. QED
        BY <1>2, <3>1
    <2>2. QED
      BY <2>1
  <1>4. QED
    BY <1>3

THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW f
                PROVE  \E A \in SUBSET S :
                         \A x \in S : f[x] # A
    OBVIOUS
  <1>2. Diagonal(S, f) \in SUBSET S
    BY DiagonalInSubset
  <1>3. \A x \in S : f[x] # Diagonal(S, f)
    BY DiagonalDiffers
  <1>4. QED
    BY <1>2, <1>3
===============================================
