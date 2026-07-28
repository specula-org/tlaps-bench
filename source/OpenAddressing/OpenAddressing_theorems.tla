---------------------- MODULE OpenAddressing_theorems ----------------------
(***************************************************************************)
(* Benchmark targets for the OpenAddressing model.                         *)
(*                                                                         *)
(* `OpenAddressing.tla` is the upstream specification and defines each of   *)
(* the safety properties below, but declares no theorem, so on its own it   *)
(* yields no proof-from-scratch task. This module asserts the properties    *)
(* the benchmark targets, leaving the upstream file untouched.              *)
(*                                                                         *)
(* Upstream also ships `OpenAddressing_proof.tla` with real proofs of these *)
(* goals. It is not imported yet: its bound variable `p` collides with the  *)
(* model's `p(self)` operator, so it does not parse against the model as    *)
(* published, and the adaptation is still to be confirmed. Nothing here     *)
(* depends on that resolution — proof-from-scratch strips proofs regardless.*)
(***************************************************************************)
EXTENDS OpenAddressing

THEOREM Spec => []CompleteAsSafety
PROOF OBVIOUS

THEOREM Spec => []Consistent
PROOF OBVIOUS

THEOREM Spec => []Contains
PROOF OBVIOUS

THEOREM Spec => []Duplicates
PROOF OBVIOUS

THEOREM Spec => []Sorted
PROOF OBVIOUS

=============================================================================
