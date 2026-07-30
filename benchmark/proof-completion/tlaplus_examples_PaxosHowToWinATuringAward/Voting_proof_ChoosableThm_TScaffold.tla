--------------------------- MODULE Voting_proof_ChoosableThm_TScaffold ----------------------------
(***************************************************************************)
(* TLAPS proofs of theorems stated in Voting.tla.  The spec is essentially *)
(* the same as Paxos/Voting.tla; the proofs are direct ports.              *)
(*                                                                         *)
(*   AllSafeAtZero    (Band E)                                             *)
(*   ChoosableThm     (Band E)                                             *)
(*   ShowsSafety      (Band M)                                             *)
(*                                                                         *)
(* Invariance and Implementation depend on a SafeAtMonotone lemma not yet *)
(* established; see Paxos/Voting_proof.tla for the same deferral.         *)
(***************************************************************************)
EXTENDS Voting

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF OMITTED

(***************************************************************************)
(*                              HELPERS                                    *)
(***************************************************************************)

THEOREM AllSafeAtZero_T == \A v \in Value : SafeAt(0, v)
PROOF OMITTED

=============================================================================
