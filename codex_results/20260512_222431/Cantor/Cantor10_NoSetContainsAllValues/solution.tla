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
  <1>1. SUFFICES ASSUME NEW S PROVE \E x : x \notin S
    OBVIOUS
  <1>2. Cantor
    BY Cantor
  <1>3. DEFINE f == [x \in S |-> x]
  <1>4. \A g : \E A \in SUBSET S : \A x \in S : g [x] # A
    BY <1>2 DEF Cantor
  <1>5. PICK A \in SUBSET S : \A x \in S : f [x] # A
    BY <1>4
  <1>6. A \notin S
    BY <1>5 DEF f
  <1>7. \E x : x \notin S
    BY <1>6
  <1>8. QED
    BY <1>7

=============================================================================
