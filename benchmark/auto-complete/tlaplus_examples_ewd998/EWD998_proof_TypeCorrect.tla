---------------------------- MODULE EWD998_proof_TypeCorrect ----------------------------
(***************************************************************************)
(* Proofs checked by TLAPS about the EWD998 specification.                 *)
(***************************************************************************)
EXTENDS EWD998_proof

USE NAssumption

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
THEOREM TypeCorrect == Init /\ [][Next]_vars => []TypeOK
PROOF OBVIOUS

(***************************************************************************)
(* Lemmas about FoldFunction that should go to a library.                  *)
(***************************************************************************)
IsAssociativeOn(op(_,_), S) ==
  \A x,y,z \in S : op(x, op(y,z)) = op(op(x,y), z)
  
IsCommutativeOn(op(_,_), S) ==
  \A x,y \in S : op(x,y) = op(y,x)
  
IsIdentityOn(op(_,_), e, S) ==
  \A x \in S : op(e,x) = x

(***************************************************************************)
(* The provers have trouble applying these generic lemmas to the specific  *)
(* instances required for the spec so we restate them for the operators    *)
(* that appear in the definition of the inductive invariant.               *)
(***************************************************************************)

\* BY FoldFunctionOnSetIterate, NodeIsFinite, PlusACI DEF Sum (* fails *)

\* BY FoldFunctionOnSetEqual, NodeIsFinite DEF Sum (* fails *)

(***************************************************************************)
(* Proof of the inductive invariant.                                       *)
(***************************************************************************)

(***************************************************************************)
(* In particular, the invariant explains why the algorithm is safe.        *)
(***************************************************************************)

(***************************************************************************)
(* A useful lemma for the liveness and refinement proofs.                  *)
(***************************************************************************)

(***************************************************************************)
(* Proofs of liveness.                                                     *)
(***************************************************************************)

(***************************************************************************)
(* We first establish the enabledness condition for the System action.     *)
(* We exclude a special case that we are not interested in. In fact, it    *)
(* would be reasonable to assume N>1.                                      *)
(***************************************************************************)

(***************************************************************************)
(* In particular, a system transition is enabled when the token is at the  *)
(* master node and termination has not been detected.                      *)
(***************************************************************************)

(***************************************************************************)
(* Assuming the system has terminated, termination detection may require   *)
(* up to three rounds of the token:                                        *)
(* 1. The first round simply brings the token back to the master node.     *)
(* 2. The second round brings the token back to the master, with all nodes *)
(*    being colored white.                                                 *)
(* 3. The third round verifies that all nodes are white and brings back a  *)
(*    white token to the master node. Moreover, the counter held by the    *)
(*    token corresponds to the sum of the non-master nodes.                *)
(* At the end of the third round, the invariant ensures that the master    *)
(* node detects termination.                                               *)
(* The proof becomes a little simpler if we assume, aiming for a           *)
(* contradiction, that termination is never detected. This motivates the   *)
(* definition of the following operator BSpec.                             *)
(***************************************************************************)

atMaster == token.pos = 0
tknWhite == token.color = "white"
tknCount == token.q = Sum(counter, Rng(1,N-1))
allWhite == \A i \in Node : color[i] = "white"

(***************************************************************************)
(* Refinement proof.                                                       *)
(* In order to reuse lemmas about the high-level specification, we         *)
(* instantiate the corresponding proof module.                             *)
(***************************************************************************)

(***************************************************************************)
(* The (state-level) safety invariant `TerminationDetection`:              *)
(* `terminationDetected => Termination`.  Direct corollary of Safety       *)
(* together with the type and Inv invariance theorems.                     *)
(***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Fri Jul 01 09:08:35 CEST 2022 by merz
\* Created Wed Apr 13 08:20:53 CEST 2022 by merz
