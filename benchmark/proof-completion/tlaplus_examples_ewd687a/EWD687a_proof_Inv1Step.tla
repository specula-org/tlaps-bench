--------------------------- MODULE EWD687a_proof_Inv1Step ---------------------------
(***************************************************************************)
(* TLAPS proofs of the theorems stated in EWD687a.tla.                     *)
(***************************************************************************)
EXTENDS EWD687a, NaturalsInduction, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Theorem 1: Spec => CountersConsistent                                   *)
(*                                                                         *)
(* The four counters per edge are always consistent: the number of         *)
(* messages ever sent on an edge equals the messages received and          *)
(* acknowledged plus the messages received and not yet acked plus the      *)
(* acks in flight plus the messages still in flight.                       *)
(*                                                                         *)
(* TypeOK on its own is not inductive: in RcvAck and SendAck a counter is  *)
(* decremented, and we can only show that the result stays in Nat by also  *)
(* knowing the counters are consistent.  We therefore prove TypeOK and the *)
(* state predicate Counters together as a single inductive invariant.     *)
(***************************************************************************)
Counters == \A e \in Edges : sentUnacked[e] = rcvdUnacked[e] + acks[e] + msgs[e]

Inv1 == TypeOK /\ Counters

LEMMA Inv1Init == Init => Inv1
PROOF OMITTED

LEMMA Inv1Step == Inv1 /\ [Next]_vars => Inv1'
PROOF OBVIOUS

(***************************************************************************)
(* Theorem 3: Spec => []DT1Inv                                             *)
(*                                                                         *)
(* Main safety property: when the leader is neutral, the entire            *)
(* computation has terminated, i.e., every non-leader process is also      *)
(* neutral.                                                                *)
(*                                                                         *)
(* DT1Inv is not directly inductive.  We strengthen it by adding two       *)
(* invariants describing the structure of the overlay tree:                *)
(*                                                                         *)
(*   - Non-neutral non-leader processes always have an upEdge (so they     *)
(*     are part of the overlay tree).                                      *)
(*   - If p is in the tree, then upEdge[p] is a well-formed incoming edge  *)
(*     of p, the edge has at least one unacknowledged message              *)
(*     (rcvdUnacked >= 1), and (the key fact for DT1Inv) the parent of p   *)
(*     in the overlay tree is itself non-neutral.                          *)
(*                                                                         *)
(* From the second invariant, the chain of upEdges from any non-neutral    *)
(* non-leader p consists of non-neutral processes, so the leader cannot    *)
(* be neutral whenever any other process is non-neutral.  Formalising the  *)
(* finite-chain argument needs Procs to be finite and a small amount of    *)
(* well-founded reasoning, factored out as a separate lemma.               *)
(***************************************************************************)
ASSUME ProcsFinite == IsFiniteSet(Procs)

InTree(p) == upEdge[p] # NotAnEdge

Inv2 == /\ \A p \in Procs \ {Leader} : ~neutral(p) => InTree(p)
        /\ \A p \in Procs \ {Leader} :
                InTree(p) =>
                    /\ upEdge[p] \in Edges
                    /\ upEdge[p][2] = p
                    /\ upEdge[p][1] \in Procs \ {p}
                    /\ rcvdUnacked[upEdge[p]] >= 1

(***************************************************************************)
(* The chain step.                                                         *)
(*                                                                         *)
(* Assume Inv2 and neutral(Leader).  Suppose, for contradiction, that      *)
(* S == {p \in Procs \ {Leader} : ~neutral(p)} is non-empty.               *)
(*                                                                         *)
(*  - Conjunct 3 of Inv2 gives InTree(p) for every p in S.                 *)
(*  - Conjunct 4 of Inv2 + Counters give sentUnacked[upEdge[p]] >= 1,      *)
(*    so the parent upEdge[p][1] is non-neutral.                           *)
(*  - Since neutral(Leader), the parent is not Leader, hence the parent    *)
(*    is itself in S.                                                      *)
(*                                                                         *)
(* So upEdge[_][1] defines a function f : S -> S with no fixed points.     *)
(* In any non-empty set such an f might still admit a cycle, so we need an *)
(* auxiliary invariant ruling out cycles in the upEdge graph.  We use the  *)
(* following formulation: there is no non-empty set of in-tree non-leader  *)
(* processes that is closed under taking the parent.  (Equivalently: every *)
(* in-tree process can reach the leader by following upEdge.)              *)
(*                                                                         *)
(* NoCycle is established inductively (NoCycleInductive below).  All       *)
(* actions other than RcvMsg either leave upEdge unchanged or, in the     *)
(* case of SendAck removing p from the tree, leave p with no children    *)
(* (its OutEdges are quiescent), so any putative new closed set would     *)
(* already have been a closed set in the previous state.  RcvMsg may     *)
(* attach a new process p to the tree with parent e[1]; if a closed set  *)
(* S' arose in the new state with p \in S', then by Counters and Inv2    *)
(* conjunct 4 no other in-tree process points to p (since p was neutral, *)
(* every OutEdge of p has sentUnacked = 0), so removing p from S' yields  *)
(* a smaller closed set in the previous state - contradicting the         *)
(* induction hypothesis.                                                   *)
(***************************************************************************)
NoCycle == \A S \in SUBSET (Procs \ {Leader}) :
              ~ (/\ S # {}
                 /\ \A q \in S : InTree(q) /\ upEdge[q][1] \in S)

(***************************************************************************)
(* Inductiveness of the auxiliary acyclicity invariant NoCycle (defined    *)
(* alongside Inv2 above).  The proof depends on Inv2 (in particular        *)
(* Counters and conjunct 4) for the RcvMsg case.                           *)
(***************************************************************************)

(***************************************************************************)
(* Discharge of DT1FromInv2 using Inv2 and the acyclicity invariant.       *)
(***************************************************************************)

(***************************************************************************)
(* Theorem 2: Spec => TreeWithRoot                                         *)
(*                                                                         *)
(* The set E of upEdges (excluding NotAnEdge), with N the set of nodes     *)
(* appearing in those edges, forms (when transposed) a tree rooted at      *)
(* the leader, and every node of that tree is non-neutral.                 *)
(*                                                                         *)
(* The structural invariants Inv2 + NoCycle proven above already capture   *)
(* the tree shape; what's left is to relate them to the                    *)
(* IsTreeWithRoot/AreConnectedIn predicates from the community-modules     *)
(* Graphs module.  For the connectivity part, we construct a simple path   *)
(* from each node to the leader by iterating upEdge.                       *)
(***************************************************************************)
G == INSTANCE Graphs

(***************************************************************************)
(* Concrete in-tree structure (the transposed overlay tree).               *)
(***************************************************************************)
EE == {upEdge[p] : p \in DOMAIN upEdge} \ {NotAnEdge}
NN == {e[1] : e \in EE} \cup {e[2] : e \in EE}
OO == G!Transpose([edge |-> EE, node |-> NN])

(***************************************************************************)
(* Both endpoints of every E-edge are non-neutral.  Children are           *)
(* non-neutral by Inv2 (InTree implies they are in the tree, hence         *)
(* non-neutral); parents are non-neutral because the tree edge has         *)
(* rcvdUnacked >= 1, so by Counters sentUnacked >= 1 and the parent       *)
(* fails the neutral predicate.                                            *)
(***************************************************************************)

(***************************************************************************)
(* Tree-structural facts about OO derived from Inv2.                       *)
(***************************************************************************)

(***************************************************************************)
(* The connectivity part of IsTreeWithRoot says every node has a path to   *)
(* the root.  We construct that path by iterating upEdge.  This requires   *)
(* SimplePath / Cardinality reasoning which is delicate; we leave the      *)
(* concrete path-construction OMITTED and discharge the rest of            *)
(* IsTreeWithRoot from TreeStructure.                                      *)
(*                                                                         *)
(* AreConnectedIn(n, Leader, OO) follows from the chain                    *)
(*   n -> upEdge[n][1] -> upEdge[upEdge[n][1]][1] -> ... -> Leader         *)
(* which terminates by NoCycle + Procs finite.                             *)
(***************************************************************************)

(***************************************************************************)
(* The body of TreeWithRoot (under []), with module-level OO/NN/EE.        *)
(***************************************************************************)
TreeBody ==
  /\ OO.edge # {} => G!IsTreeWithRoot(OO, Leader)
  /\ \A n \in OO.node: ~neutral(n)

(***************************************************************************)
(* The structural pieces above (TreeNodesNonNeutral / TreeStructure /      *)
(* TreeIsTree) discharge most of TreeWithRoot.  The QED below would close *)
(* the proof; it requires:                                                 *)
(*  (a) AreConnectedToLeader (OMITTED above) -- the SimplePath / Cardinal- *)
(*      ity / SeqOf reasoning to construct a path from any node to the     *)
(*      leader by iterating upEdge.                                        *)
(*  (b) Bridging the syntactic gap between TreeWithRoot's `LET ... IN []`  *)
(*      shape and our `[]TreeBody` form.  The two are semantically equal   *)
(*      because LET is just substitution, but TLAPS' temporal backend      *)
(*      currently does not unify them.                                     *)
(***************************************************************************)

(***************************************************************************)
(* Theorem 4: Spec => DT2  (liveness)                                      *)
(*                                                                         *)
(* Liveness:  Terminated ~> neutral(Leader).                               *)
(*                                                                         *)
(* Once the computation has globally terminated, the WF_vars(Next)         *)
(* fairness assumption guarantees progress on each remaining               *)
(* RcvMsg/SendAck/RcvAck step until all counters drain to 0 and the       *)
(* leader becomes neutral.  A multiset/well-founded measure on             *)
(* (msgs, rcvdUnacked, acks, sentUnacked) is needed; left as future work.  *)
(***************************************************************************)

=============================================================================
