(* Contributed by Stephan Merz *)

-------------- MODULE Cantor4_cantor ------------------
THEOREM cantor ==
 \A S :
   \A f \in [S -> SUBSET S] :
     \E A \in SUBSET S :
       \A x \in S :
         f [x] # A
PROOF
  <1>1. TAKE S
  <1>1. SUFFICES ASSUME NEW f \in [S -> SUBSET S]
                PROVE  \E A \in SUBSET S : \A x \in S : f[x] # A
    OBVIOUS
  <1>2. DEFINE A == {x \in S : x \notin f[x]}
  <1>3. A \in SUBSET S
    OBVIOUS
  <1>4. \A x \in S : f[x] # A
  PROOF
    <2>1. TAKE x \in S
    <2>2. SUFFICES ASSUME f[x] = A
                  PROVE  FALSE
      OBVIOUS
    <2>3. x \in f[x] <=> x \in A
      BY <2>2
    <2>4. x \in A <=> x \notin f[x]
      BY <2>1 DEF A
    <2>5. FALSE
      BY <2>3, <2>4
    <2> QED
      BY <2>2, <2>5
  <1>5. QED
    BY <1>3, <1>4

===============================================
