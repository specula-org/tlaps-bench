

-------------- MODULE Cantor4_cantor ------------------
Diag(S, f) == {x \in S : x \notin f[x]}

THEOREM cantor ==
 \A S :
   \A f \in [S -> SUBSET S] :
     \E A \in SUBSET S :
       \A x \in S :
         f [x] # A
PROOF
  <1>1. TAKE S
  <1>2. TAKE f \in [S -> SUBSET S]
  <1>3. Diag(S, f) \in SUBSET S
    BY DEF Diag
  <1>4. \A x \in S : f[x] # Diag(S, f)
    <2>1. TAKE x \in S
    <2>2. x \in Diag(S, f) <=> x \notin f[x]
      BY <2>1 DEF Diag
    <2>3. f[x] # Diag(S, f)
      BY <2>2
    <2> QED BY <2>3
  <1>5. QED
    BY <1>3, <1>4
===============================================
