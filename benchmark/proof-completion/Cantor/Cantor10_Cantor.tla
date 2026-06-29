------------------------------ MODULE Cantor10_Cantor ------------------------------
(***************************************************************************)
(* Cantor's theorem: no function from a set to its powerset is surjective. *)
(***************************************************************************)
THEOREM Cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF OBVIOUS

(***************************************************************************)
(* Corollary: no set is universal.                                         *)
(***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Sun Aug 29 17:27:32 PDT 2010 by lamport
\* Created Sun Aug 29 17:25:20 PDT 2010 by lamport
