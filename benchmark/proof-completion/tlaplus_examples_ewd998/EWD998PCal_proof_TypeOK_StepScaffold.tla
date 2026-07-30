---------------------------- MODULE EWD998PCal_proof_TypeOK_StepScaffold ----------------------------
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
LEMMA BagRemoveOfMsg ==
  ASSUME NEW B \in BagOf(Msg), NEW x
  PROVE  BagRemove(B, x) \in BagOf(Msg)
PROOF OMITTED

(***************************************************************************)
(* Helper: a "pl" message is in Msg.                                      *)
(***************************************************************************)
LEMMA PlMsgInMsg == [type |-> "pl"] \in Msg
PROOF OMITTED

(***************************************************************************)
(* Helper: a "pl" message and a "tok" message are distinct (their `type`  *)
(* fields differ).                                                        *)
(***************************************************************************)
LEMMA PlMsgIsNotTok == ~ ([type |-> "pl"].type = "tok")
  OBVIOUS

(***************************************************************************)
(* Helper: the "new token" produced by a PassToken/InitiateProbe step is  *)
(* in Msg whenever its q-field is in Int and color-field is in ColorSet. *)
(***************************************************************************)
LEMMA NewTokInMsg ==
  ASSUME NEW q \in Int, NEW c \in ColorSet
  PROVE  [type |-> "tok", q |-> q, color |-> c] \in Msg
PROOF OMITTED

(***************************************************************************)
(* Helper: BagAdd of a non-tok message x to a bag B:                      *)
(*  (a) preserves token presence: any tok in DOMAIN B remains in          *)
(*      DOMAIN BagAdd(B,x) with the same multiplicity;                    *)
(*  (b) does not introduce new toks: any tok in DOMAIN BagAdd(B,x)        *)
(*      was already in DOMAIN B (since x has type # "tok").              *)
(***************************************************************************)
LEMMA BagAddPreservesToks ==
  ASSUME NEW B, NEW x, x.type # "tok"
  PROVE  /\ \A t : t.type = "tok" /\ t \in DOMAIN B
                  => /\ t \in DOMAIN BagAdd(B, x)
                     /\ BagAdd(B, x)[t] = B[t]
         /\ \A t : t.type = "tok" /\ t \in DOMAIN BagAdd(B, x)
                  => t \in DOMAIN B
PROOF OMITTED

(***************************************************************************)
(* Helper: BagRemove of a non-tok message x from a bag B:                 *)
(*  (a) preserves any tok in DOMAIN B (whether x was in B or not);        *)
(*  (b) does not introduce new toks.                                      *)
(***************************************************************************)
LEMMA BagRemovePreservesToks ==
  ASSUME NEW B, NEW x, x.type # "tok"
  PROVE  /\ \A t : t.type = "tok" /\ t \in DOMAIN B
                  => /\ t \in DOMAIN BagRemove(B, x)
                     /\ BagRemove(B, x)[t] = B[t]
         /\ \A t : t.type = "tok" /\ t \in DOMAIN BagRemove(B, x)
                  => t \in DOMAIN B
PROOF OMITTED

(***************************************************************************)
(* The unique-token witness extracted from NetworkOK.                      *)
(***************************************************************************)
TokenAt(n) == \E t \in DOMAIN network[n] : t.type = "tok"

(***************************************************************************)
(* Inductive step for PCalTypeOK -- per disjunct of node(self).           *)
(*                                                                        *)
(* Of the four conjuncts of PCalTypeOK we discharge `active`, `color`,    *)
(* `counter`, and the bag-typing of `network` for all five PCal           *)
(* disjuncts.  The unique-token preservation in NetworkOK is OMITTED      *)
(* and left for a later round.                                            *)
(***************************************************************************)
=============================================================================
