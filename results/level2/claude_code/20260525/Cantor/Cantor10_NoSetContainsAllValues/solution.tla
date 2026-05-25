------------------------------ MODULE Cantor10_NoSetContainsAllValues ------------------------------
(***************************************************************************)
(* Cantor's theorem: no function from a set to its powerset is surjective. *)
(***************************************************************************)

(***************************************************************************)
(* Corollary: no set is universal.                                         *)
(***************************************************************************)
THEOREM NoSetContainsAllValues ==
  \A S : \E x : x \notin S
PROOF
<1>1. ASSUME NEW S
      PROVE \E x : x \notin S
  <2> DEFINE R == {x \in S : x \notin x}
  <2>1. ASSUME \A x : x \in S
        PROVE FALSE
    <3>1. R \in S BY <2>1
    <3>2. R \in R <=> (R \in S /\ R \notin R) BY DEF R
    <3>3. QED BY <3>1, <3>2
  <2>2. QED BY <2>1
<1>2. QED BY <1>1


=============================================================================
\* Modification History
\* Last modified Sun Aug 29 17:27:32 PDT 2010 by lamport
\* Created Sun Aug 29 17:25:20 PDT 2010 by lamport
