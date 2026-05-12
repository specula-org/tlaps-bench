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
PROOF OBVIOUS

=============================================================================