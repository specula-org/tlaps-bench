------------------------- MODULE etcdraft_theorems -------------------------
(***************************************************************************)
(* Benchmark targets for the etcd-raft model.                              *)
(*                                                                         *)
(* `etcdraft.tla` is the upstream specification. It defines all of the      *)
(* invariants below and already declares `THEOREM Spec => []LogInv`, so     *)
(* `LogInv` is generated from the upstream file itself and is deliberately  *)
(* not repeated here. The remaining seven properties are asserted here so   *)
(* the benchmark keeps its eight etcd-raft targets, with the upstream file  *)
(* left untouched.                                                         *)
(***************************************************************************)
EXTENDS etcdraft

THEOREM Spec => []CommittedIsDurableInv
PROOF OBVIOUS

THEOREM Spec => []ElectionSafetyInv
PROOF OBVIOUS

THEOREM Spec => []LeaderCompletenessInv
PROOF OBVIOUS

THEOREM Spec => []LogMatchingInv
PROOF OBVIOUS

THEOREM Spec => []MoreThanOneLeaderInv
PROOF OBVIOUS

THEOREM Spec => []MoreUpToDateCorrectInv
PROOF OBVIOUS

THEOREM Spec => []QuorumLogInv
PROOF OBVIOUS

=============================================================================
