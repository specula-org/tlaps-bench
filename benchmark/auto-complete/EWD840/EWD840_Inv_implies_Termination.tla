------------------------------- MODULE EWD840_Inv_implies_Termination -------------------------------
EXTENDS EWD840

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Nodes -> Color]       \* color of nodes
  /\ tpos \in Nodes                    \* token position
  /\ tcolor \in Color                  \* token color

(* Initially the token is at node 0, and it is black. There
   are no constraints on the status and color of the nodes. *)

(* Node 0 may initiate a probe when it has the token and when
   it is black or the token color is black. It passes
   a white token to node N-1 and paints itself white. *)

(* An inactive node different from 0 that possesses the token
   may pass it to node i-1 under the following circumstances:
   - node i is inactive or
   - node i is colored black or
   - the token is black.
   Note that the last two conditions will result in an
   inconclusive round, since the token will be black.
   The token will be stained if node i is black, otherwise 
   its color is unchanged. Node i will be made white. *)

(* An active node i may activate another node j by sending it
   a message. If j>i (hence activation goes against the direction
   of the token being passed), then node i becomes black. *)

(* Any active node may become inactive at any moment. *)

(* Actions controlled by termination detection algorithm *)

(* Remaining actions, corresponding to environment transitions *)

(***************************************************************************)
(* Non-invariants for validating the specification.                        *)
(***************************************************************************)
NeverBlack == \A i \in Nodes : color[i] # "black"

NeverChangeColor == [][ \A i \in Nodes : UNCHANGED color[i] ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* undesired, but verified for the fairness condition WF_vars(Next).       *)
(* This motivates weakening the fairness condition to WF_vars(Controlled). *)
(***************************************************************************)
AllNodesTerminateIfNoMessages ==
  <>[][~ \E i \in Nodes : SendMsg(i)]_vars
  => <>(\A i \in Nodes : ~ active[i])

(***************************************************************************)
(* Dijkstra's invariant                                                    *)
(***************************************************************************)
Inv == 
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

(* TypeOK is an inductive invariant *)
LEMMA TypeOK_inv == Spec => []TypeOK
PROOF OMITTED

THEOREM Spec => []TerminationDetection
PROOF OMITTED

(* If the one-line proof of step <1>1 above is too obscure, 
    here is a more detailed, hierarchical proof of the same property. *)
LEMMA Inv_implies_Termination == Inv => TerminationDetection

PROOF OBVIOUS

=============================================================================
\* Modification History
\* Last modified Wed Aug 06 12:26:15 CEST 2014 by merz
\* Last modified Fri May 30 23:04:12 CEST 2014 by shaolin
\* Last modified Wed May 21 11:36:56 CEST 2014 by jael
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
