------------------------- MODULE PaxosCommit_proof_MajorityNonEmpty -------------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM PCSpec => []PCTypeOK                                          *)
(* stated (as a non-temporal version) in PaxosCommit.tla.                  *)
(*                                                                         *)
(* The inductive strengthening follows the template of the Paxos           *)
(* consensus proof in tlapm/examples/paxos/Paxos.tla.  Beyond PCTypeOK     *)
(* itself we maintain                                                      *)
(*                                                                         *)
(*   AccInv:   for every acceptor state, val = "none" iff bal = -1         *)
(*             (analogue of the first conjunct of AccInv in the Paxos      *)
(*             proof, with None  --> "none" and Values  --> {"prepared",   *)
(*             "aborted"}),                                                *)
(*                                                                         *)
(*   MsgInv1b: every "phase1b" message m with m.bal # -1 has               *)
(*             m.val \in {"prepared", "aborted"}                           *)
(*             (the projection onto Paxos Commit of the first disjunct of  *)
(*             MsgInv for "1b" messages in the Paxos proof).               *)
(*                                                                         *)
(* MsgInv1b is the auxiliary fact alluded to in the original comment of    *)
(* this module: it is what is needed to discharge type-correctness for     *)
(* Phase2a, namely that the value the leader picks for the new "phase2a"  *)
(* message lies in {"prepared", "aborted"}.                                *)
(*                                                                         *)
(* We additionally carry IsFiniteSet(msgs) so that the Maximum operator    *)
(* used in Phase2a behaves as expected on the finite set of phase 1b       *)
(* ballot numbers.                                                         *)
(***************************************************************************)
EXTENDS PaxosCommit, FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

vars == <<rmState, aState, msgs>>

AccInv ==
  \A rm \in RM, ac \in Acceptor :
       aState[rm][ac].val = "none" <=> aState[rm][ac].bal = -1

MsgInv1b ==
  \A m \in msgs :
       (m.type = "phase1b" /\ m.bal # -1) => m.val \in {"prepared", "aborted"}

Inv == PCTypeOK /\ AccInv /\ MsgInv1b /\ IsFiniteSet(msgs)

(***************************************************************************)
(* The following lemma states the standard fact that for a non-empty       *)
(* finite set of integers all of which are at least -1, the recursive      *)
(* Maximum operator returns an upper bound that is itself in the set.      *)
(*                                                                         *)
(* Notes on the precondition.  Maximum's recursion uses -1 as the result   *)
(* on the empty set, so the result is always in S \cup {-1}.  When some    *)
(* element of S is below -1, Maximum can return -1 (which lies above any  *)
(* such element); the result then need not be in S itself.  All callers   *)
(* in the surrounding spec apply Maximum to a set of phase-1b ballots,    *)
(* which lies in Ballot \cup {-1} \subseteq Nat \cup {-1}, so the         *)
(* "elements >= -1" precondition is always satisfied there.                *)
(*                                                                         *)
(* The proof has two pieces: (i) MaximumRec gives the recursion equation   *)
(* of the inner CHOOSE-defined function `Max[T]` via WFInductiveDef, and   *)
(* (ii) MaximumProp uses well-founded induction over the strict-subset    *)
(* ordering to derive the upper-bound / membership properties.            *)
(***************************************************************************)
MaxDef(g, T) ==
  IF T = {} THEN -1
  ELSE LET n    == CHOOSE n2 \in T : TRUE
           rmax == g[T \ {n}]
       IN  IF n \geq rmax THEN n ELSE rmax

\* The CHOOSE form of the inner recursive function in Maximum(S).
MaxFn(S) == CHOOSE g : g = [T \in SUBSET S |-> MaxDef(g, T)]

LEMMA MaxFnRec ==
  ASSUME NEW S, IsFiniteSet(S), NEW T \in SUBSET S
  PROVE  MaxFn(S)[T] = MaxDef(MaxFn(S), T)
PROOF OMITTED

LEMMA MaximumIsMaxFn ==
  ASSUME NEW S
  PROVE  Maximum(S) = MaxFn(S)[S]
PROOF OMITTED

LEMMA MaximumProp ==
  ASSUME NEW S, IsFiniteSet(S), S \subseteq Int, S # {},
         \A x \in S : x >= -1
  PROVE  /\ Maximum(S) \in S
         /\ \A n \in S : n =< Maximum(S)
PROOF OMITTED

(***************************************************************************)
(* Auxiliary fact used in the Phase2a case: any majority is non-empty,     *)
(* since by PaxosCommitAssumptions any two majorities have non-empty       *)
(* intersection (in particular MS \cap MS = MS).                           *)
(***************************************************************************)
LEMMA MajorityNonEmpty == \A MS \in Majority : MS # {}
PROOF OBVIOUS

(***************************************************************************)
(* Initiation: the inductive invariant holds in the initial state.         *)
(***************************************************************************)

(***************************************************************************)
(* Consecution: the inductive invariant is preserved by every step of the  *)
(* next-state relation (and trivially by stuttering steps).                *)
(***************************************************************************)

(***************************************************************************)
(* Main theorem: PCTypeOK is an invariant of PCSpec.                       *)
(***************************************************************************)

(***************************************************************************)
(* The non-temporal version of the theorem stated in PaxosCommit.tla       *)
(* (PCSpec => PCTypeOK) is an immediate corollary.                         *)
(***************************************************************************)

============================================================================
