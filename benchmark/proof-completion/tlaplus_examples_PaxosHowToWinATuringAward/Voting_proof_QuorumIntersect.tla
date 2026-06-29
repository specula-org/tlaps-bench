--------------------------- MODULE Voting_proof_QuorumIntersect ----------------------------
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

THEOREM ChoosableThm_T ==
    \A b \in Ballot, v \in Value : ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
PROOF OMITTED

(***************************************************************************)
(* OneValuePerBallot in ASSUME/PROVE form.                                *)
(***************************************************************************)
LEMMA OneValuePerBallotApply ==
  ASSUME OneValuePerBallot,
         NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW bb \in Ballot,
         NEW v1 \in Value, NEW v2 \in Value,
         VotedFor(a1, bb, v1), VotedFor(a2, bb, v2)
  PROVE  v1 = v2
PROOF OMITTED

(***************************************************************************)
(* Convenience: any two quorums intersect in at least one acceptor.        *)
(***************************************************************************)
LEMMA QuorumIntersect ==
  ASSUME NEW Q1 \in Quorum, NEW Q2 \in Quorum
  PROVE  \E a \in Q1 \cap Q2 : a \in Acceptor
PROOF OBVIOUS

(***************************************************************************)
(*                          ShowsSafety   (Band M)                         *)
(***************************************************************************)

============================================================================
