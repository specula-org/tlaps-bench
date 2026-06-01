------------------------------ MODULE Cantor10_NoSetContainsAllValues ------------------------------
(***************************************************************************)
(* Cantor's theorem: no function from a set to its powerset is surjective. *)
(***************************************************************************)
THEOREM Cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
  PROOF OMITTED

THEOREM NoSetContainsAllValues ==
  \A S : \E x : x \notin S
PROOF
  <1>1. SUFFICES ASSUME NEW S
                PROVE  \E x : x \notin S
    OBVIOUS
  <1>2. PICK A \in SUBSET S :
          \A x \in S : [y \in S |-> y][x] # A
    PROOF
      <2>1. SUFFICES ASSUME NEW f, f = [y \in S |-> y]
                    PROVE  \E A \in SUBSET S :
                             \A x \in S : [y \in S |-> y][x] # A
        OBVIOUS
      <2>2. \A T, g :
              \E A \in SUBSET T :
                \A x \in T : g[x] # A
        BY Cantor
      <2>3. \E A \in SUBSET S :
              \A x \in S : f[x] # A
        BY <2>2
      <2>4. \E A \in SUBSET S :
              \A x \in S : [y \in S |-> y][x] # A
        BY <2>1, <2>3
      <2>5. QED
        BY <2>4
  <1>3. \E x : x \notin S
  PROOF
    <2>1. SUFFICES ASSUME \A x : x \in S
                  PROVE  FALSE
      OBVIOUS
    <2>2. A \in S
      BY <2>1
    <2>3. [y \in S |-> y][A] = A
      BY <2>2
    <2>4. [y \in S |-> y][A] # A
      BY <1>2, <2>2
    <2>5. QED
      BY <2>3, <2>4
  <1>4. QED
    BY <1>3

=============================================================================
