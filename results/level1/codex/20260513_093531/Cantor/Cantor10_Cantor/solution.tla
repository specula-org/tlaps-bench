------------------------------ MODULE Cantor10_Cantor ------------------------------
(***************************************************************************)
(* Cantor's theorem: no function from a set to its powerset is surjective. *)
(***************************************************************************)
THEOREM Cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
<1> TAKE S, f
<1>1. {x \in S : x \notin f[x]} \in SUBSET S
  OBVIOUS
<1>2. \A x \in S : f[x] # {x \in S : x \notin f[x]}
  <2> TAKE x \in S
  <2>1. x \in {y \in S : y \notin f[y]} <=> x \notin f[x]
    OBVIOUS
  <2>2. f[x] # {y \in S : y \notin f[y]}
    <3>1. SUFFICES ASSUME f[x] = {y \in S : y \notin f[y]}
                 PROVE  FALSE
      OBVIOUS
    <3>2. x \in f[x] <=> x \notin f[x]
      BY <2>1, <3>1
    <3> QED BY <3>2
  <2> QED BY <2>2
<1>3. \E A \in SUBSET S : \A x \in S : f[x] # A
  BY <1>1, <1>2
<1> QED BY <1>1, <1>2

=============================================================================
