------------------------------ MODULE Cantor10_NoSetContainsAllValues ------------------------------
(***************************************************************************)
(* Cantor's theorem: no function from a set to its powerset is surjective. *)
(***************************************************************************)

(***************************************************************************)
(* Corollary: no set is universal.                                         *)
(***************************************************************************)
THEOREM NoSetContainsAllValues ==
  \A S : \E x : x \notin S
PROOF OBVIOUS


=============================================================================
\* Modification History
\* Last modified Sun Aug 29 17:27:32 PDT 2010 by lamport
\* Created Sun Aug 29 17:25:20 PDT 2010 by lamport
