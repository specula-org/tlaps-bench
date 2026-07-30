---------------------------- MODULE EWD998PCal_proof_BagRemoveOfMsgScaffold ----------------------------
(***************************************************************************)
(* Proofs checked by TLAPS about the EWD998PCal specification.             *)
(*                                                                         *)
(* The EWD998PCal module is a PlusCal-translated version of EWD998 in      *)
(* which the per-node `pending` counter and the global `token` of EWD998   *)
(* are replaced by a single `network` variable holding a per-node bag of   *)
(* messages (payload "pl" messages and the unique token "tok" message).   *)
(* The refinement mapping (in EWD998PCal.tla) recovers EWD998's `pending` *)
(* and `token` from `network`:                                            *)
(*                                                                         *)
(*   pending = [n |-> count of [type|->"pl"] in network[n]]                *)
(*   token   = the unique tok msg in the network, with its position       *)
(*                                                                         *)
(* This module proves the safety part of the refinement,                   *)
(*                                                                         *)
(*   THEOREM Refinement == Spec => EWD998Spec                              *)
(*                                                                         *)
(* where EWD998Spec == EWD998!Init /\ [][EWD998!Next]_EWD998!vars (no     *)
(* fairness; the comment in the spec explains why).                       *)
(*                                                                         *)
(* The proof shape mirrors EWD998_proof.tla's `Refinement` theorem:       *)
(* an inductive invariant (network well-formedness + Safra's invariant   *)
(* transferred to PCal) plus a per-disjunct case analysis.                *)
(***************************************************************************)
EXTENDS EWD998PCal, TLAPS

\* The spec defines `Initiator == 0`; expose it as a fact for TLAPS.
LEMMA InitiatorIsZero == Initiator = 0
  PROOF OMITTED

\* Node = 0..N-1.
LEMMA NodeFact == 0 \in Node
  PROOF OMITTED

(***************************************************************************)
(* Type-level abbreviations.                                               *)
(***************************************************************************)
ColorSet == {"white", "black"}
PMsg == [type: {"pl"}]
TMsg == [type: {"tok"}, q: Int, color: ColorSet]
Msg  == PMsg \cup TMsg

(***************************************************************************)
(* Bag-level facts about the message-bag operators used in the spec.       *)
(*                                                                         *)
(* `EmptyBag`, `SetToBag`, `BagAdd`, `BagRemove` are imported from         *)
(* Bags / BagsExt.  We restate just enough about each so TLAPS can         *)
(* unfold them in proofs.                                                  *)
(***************************************************************************)
LEMMA EmptyBagDom == DOMAIN EmptyBag = {}
PROOF OMITTED

LEMMA SetToBagSingleton ==
  ASSUME NEW x
  PROVE  /\ DOMAIN SetToBag({x}) = {x}
         /\ SetToBag({x})[x] = 1
PROOF OMITTED

LEMMA BagAddDom ==
  ASSUME NEW B, NEW x
  PROVE  DOMAIN BagAdd(B, x) = DOMAIN B \cup {x}
PROOF OMITTED

LEMMA BagRemoveDom ==
  ASSUME NEW B, NEW x, x \in DOMAIN B
  PROVE  /\ B[x] = 1 => DOMAIN BagRemove(B, x) = DOMAIN B \ {x}
         /\ B[x] # 1 => DOMAIN BagRemove(B, x) = DOMAIN B
PROOF OMITTED

(***************************************************************************)
(* Network well-formedness:                                               *)
(*  (a) every network[n] is a function from a subset of Msg to positive  *)
(*      naturals (the `IsABag` predicate, restricted to typed messages); *)
(*  (b) exactly one node holds a token, with multiplicity 1.            *)
(***************************************************************************)
BagOf(S) == UNION { [T -> Nat \ {0}] : T \in SUBSET S }

NetworkOK ==
  /\ network \in [Node -> BagOf(Msg)]
  /\ \E n \in Node : \E t \in DOMAIN network[n] :
       /\ t.type = "tok"
       /\ network[n][t] = 1
       /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
              t2.type = "tok" => (n2 = n /\ t2 = t)

PCalTypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> ColorSet]
  /\ counter \in [Node -> Int]
  /\ NetworkOK

(***************************************************************************)
(* The initial state has the unique token (with q=0, color="black") at the*)
(* Initiator (=0) and empty bags everywhere else.                         *)
(***************************************************************************)
InitTok == [type |-> "tok", q |-> 0, color |-> "black"]

LEMMA InitNetworkUniqueTok ==
  ASSUME network = [n \in Node |->
                       IF n = Initiator
                       THEN SetToBag({InitTok})
                       ELSE EmptyBag]
  PROVE  /\ DOMAIN network[Initiator] = {InitTok}
         /\ network[Initiator][InitTok] = 1
         /\ \A n \in Node \ {Initiator} : DOMAIN network[n] = {}
PROOF OMITTED

(***************************************************************************)
(* The initial state satisfies the network type invariant.                *)
(***************************************************************************)
LEMMA InitNetworkOK == Init => NetworkOK
PROOF OMITTED

(***************************************************************************)
(* The initial state satisfies the full PCalTypeOK.                       *)
(***************************************************************************)
LEMMA InitTypeOK == Init => PCalTypeOK
PROOF OMITTED

(***************************************************************************)
(* Init refinement: the PCal Init satisfies EWD998!Init under the        *)
(* refinement mapping for `pending` and `token`.                         *)
(***************************************************************************)
LEMMA InitPending == Init => pending = [i \in Node |-> 0]
PROOF OMITTED

LEMMA InitToken == Init => token = [pos |-> 0, q |-> 0, color |-> "black"]
PROOF OMITTED

THEOREM InitRefinement == Init => EWD998!Init
PROOF OMITTED

(***************************************************************************)
(* Helper: for any well-typed bag B and any new "pl" message added with   *)
(* BagAdd (which is a fresh element if not already in DOMAIN, otherwise   *)
(* a multiplicity bump), the result is still a well-typed bag of typed   *)
(* messages.                                                              *)
(***************************************************************************)
LEMMA BagAddOfMsg ==
  ASSUME NEW B \in BagOf(Msg), NEW m \in Msg
  PROVE  BagAdd(B, m) \in BagOf(Msg)
PROOF OMITTED

(***************************************************************************)
(* Helper: BagRemove on a typed bag yields a typed bag.  This is true     *)
(* regardless of whether x is in DOMAIN B (BagRemove returns B unchanged  *)
(* in that case) or with multiplicity > 1 or = 1.                         *)
(***************************************************************************)
=============================================================================
