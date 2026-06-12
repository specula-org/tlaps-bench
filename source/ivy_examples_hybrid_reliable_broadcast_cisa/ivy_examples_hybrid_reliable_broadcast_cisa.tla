---------------- MODULE ivy_examples_hybrid_reliable_broadcast_cisa ----------------
EXTENDS TLAPS, FiniteSets

(***************************************************************************)
(* TLA+ translation of Ivy's                                                *)
(* examples/liveness/hybrid_reliable_broadcast_cisa.ivy.                   *)
(*                                                                         *)
(* The Ivy model is a threshold-style hybrid reliable broadcast protocol    *)
(* from clock synchronization work by Widder and Schmid.                    *)
(*                                                                         *)
(* Quorum membership and fault classes are static in Ivy, so this TLA+      *)
(* model represents them with constants and ASSUME declarations.  The       *)
(* mutable protocol state is the set of accepted nodes, sent messages,      *)
(* and received messages.                                                   *)
(*                                                                         *)
(* Ivy states the liveness assumptions as temporal premises.  This module   *)
(* states the corresponding scheduling assumptions directly in Spec using   *)
(* weak fairness for the correct-node send and receive actions.  Ivy's      *)
(* ghost relation d, used only to exploit finite node coverage in liveness  *)
(* proofs, is represented here by the direct NodeFinite assumption.         *)
(***************************************************************************)

(***************************************************************************)
(* Static model constants.                                                  *)
(*                                                                         *)
(*  - Node is the set of processes participating in the broadcast.          *)
(*                                                                         *)
(*  - QuorumA and QuorumB are abstract quorum identifier sets.  A-quorums   *)
(*    are relay quorums: receiving from every member of some A-quorum lets  *)
(*    a node broadcast/relay.  B-quorums are acceptance quorums: receiving  *)
(*    from every member of some B-quorum lets a node accept.                *)
(*                                                                         *)
(*  - MemberA[n][q] and MemberB[n][q] are static membership predicates      *)
(*    saying whether node n belongs to quorum q in the corresponding        *)
(*    quorum family.                                                        *)
(*                                                                         *)
(*  - FaultC, FaultI, FaultS, and FaultA are disjoint static fault-class    *)
(*    sets.  Nodes outside all four are Correct.                            *)
(*                                                                         *)
(*    FaultC: clean-crash / symmetric omission faults.  These nodes are     *)
(*    obedient: when they send a protocol message, the message content is   *)
(*    not forged.  Their fault is only in delivery coverage.  Each send is  *)
(*    symmetric: after receiving enough messages to relay, the node either  *)
(*    sends the same protocol message to every destination or sends it to   *)
(*    no destination.  Repeated full omissions model a crash.  In this      *)
(*    TLA+ model, ReceiveMsgC records received messages and nondetermin-    *)
(*    istically chooses whether an A-quorum trigger causes a full send.     *)
(*                                                                         *)
(*    FaultI: crash / asymmetric omission faults.  These nodes are also     *)
(*    obedient, so they do not forge protocol messages, but they may send   *)
(*    correct messages to only a subset of destinations.  Different        *)
(*    destinations can therefore observe different omissions.  Old sends    *)
(*    are monotonic: once a message is sent to a destination, it remains    *)
(*    sent.  In this model, ReceiveInitI and ReceiveMsgI choose an          *)
(*    arbitrary superset of the node's previous outgoing row.               *)
(*                                                                         *)
(*    FaultS: symmetric Byzantine faults.  These nodes may invent protocol  *)
(*    state or messages, so they are not obedient.  They are still          *)
(*    symmetric: when they send, they broadcast the same invented message   *)
(*    to all destinations or omit it entirely.  In this model,              *)
(*    FaultySendS broadcasts from the faulty node to every destination,     *)
(*    and FaultyStateSA can arbitrarily change that node's accept state     *)
(*    and the messages it appears to have received.                         *)
(*                                                                         *)
(*    FaultA: arbitrary Byzantine faults.  These are the strongest faults.  *)
(*    A node may invent state/messages and may send inconsistently to       *)
(*    different destinations.  As with FaultI, outgoing sends are modeled   *)
(*    monotonically: the arbitrary new outgoing row must preserve all old   *)
(*    sent messages.  FaultySendA models arbitrary per-destination sends,   *)
(*    while FaultyStateSA models arbitrary local Byzantine state changes.   *)
(*                                                                         *)
(*  - RcvInit is the static set of nodes that receive the initial broadcast *)
(*    input.  Receiving init is modeled by ReceiveInit/ReceiveInitI; this   *)
(*    constant says which nodes are eligible for those actions.             *)
(***************************************************************************)

CONSTANTS
  Node, QuorumA, QuorumB,
  MemberA, MemberB,
  FaultA, FaultC, FaultS, FaultI,
  RcvInit

ASSUME TypeAssumption ==
  /\ Node # {}
  /\ QuorumA # {}
  /\ QuorumB # {}
  /\ MemberA \in [Node -> [QuorumA -> BOOLEAN]]
  /\ MemberB \in [Node -> [QuorumB -> BOOLEAN]]
  /\ FaultA \subseteq Node
  /\ FaultC \subseteq Node
  /\ FaultS \subseteq Node
  /\ FaultI \subseteq Node
  /\ RcvInit \subseteq Node

(***************************************************************************)
(* Ivy models finite node coverage with a ghost relation d and a fair      *)
(* add_to_d action, then assumes <> \A n : d(n).  The protocol does not    *)
(* use that relation.  In TLA+, the same intended finite-domain condition  *)
(* is stated directly: Node is finite.  This is needed for liveness proofs *)
(* that combine per-node eventual deliveries into one state containing a   *)
(* complete quorum of deliveries.                                          *)
(***************************************************************************)

ASSUME NodeFinite == IsFiniteSet(Node)

InA(n, q) == MemberA[n][q]
InB(n, q) == MemberB[n][q]

Obedient(n) ==
  /\ n \notin FaultS
  /\ n \notin FaultA

Symmetric(n) ==
  /\ n \notin FaultI
  /\ n \notin FaultA

Correct(n) ==
  /\ n \notin FaultC
  /\ n \notin FaultI
  /\ n \notin FaultS
  /\ n \notin FaultA

(***************************************************************************)
(* QuorumAssumption is the threshold intersection axiom package from the   *)
(* Ivy model.  It does not describe mutable protocol state; it constrains  *)
(* which static quorum systems and fault-class assignments are admissible. *)
(*                                                                         *)
(*  - Some B-quorum is entirely correct.  This gives the model at least    *)
(*    one large set of nodes that can eventually send and receive honestly. *)
(*                                                                         *)
(*  - Every A-quorum contains at least one Obedient node, meaning a node    *)
(*    that is not FaultA and not FaultS.  Therefore an A-quorum cannot be   *)
(*    made only of nodes that can freely forge arbitrary protocol state.    *)
(*                                                                         *)
(*  - Every B-quorum contains an A-quorum whose members are Symmetric,      *)
(*    meaning they are neither arbitrary Byzantine nor asymmetric-omission  *)
(*    faulty.  This is the key intersection condition used by relay: once  *)
(*    a node has a B-quorum of received messages, there is a sufficiently  *)
(*    clean A-quorum inside it that can justify further broadcasts.         *)
(*                                                                         *)
(*  - The final six conjuncts say that the four fault classes are pairwise  *)
(*    disjoint.  A node is in at most one of FaultC, FaultI, FaultS, and    *)
(*    FaultA; nodes outside all four classes are Correct.                   *)
(***************************************************************************)

ASSUME QuorumAssumption ==
  /\ \E b \in QuorumB :
       \A n \in Node :
         InB(n, b) => Correct(n)
  /\ \A a \in QuorumA :
       \E n \in Node :
         /\ InA(n, a)
         /\ Obedient(n)
  /\ \A b \in QuorumB :
       \E a \in QuorumA :
         \A n \in Node :
           InA(n, a) =>
             /\ InB(n, b)
             /\ Symmetric(n)
  /\ \A n \in Node : ~(n \in FaultC /\ n \in FaultI)
  /\ \A n \in Node : ~(n \in FaultC /\ n \in FaultS)
  /\ \A n \in Node : ~(n \in FaultC /\ n \in FaultA)
  /\ \A n \in Node : ~(n \in FaultI /\ n \in FaultS)
  /\ \A n \in Node : ~(n \in FaultI /\ n \in FaultA)
  /\ \A n \in Node : ~(n \in FaultS /\ n \in FaultA)

(***************************************************************************)
(* Mutable protocol state.  The quorum and fault-class constants above are *)
(* fixed for the whole behavior; only these three variables change.        *)
(*                                                                         *)
(*  - accept[n] records whether node n has accepted/delivered the          *)
(*    broadcast.  Correct and obedient nodes set this only after receiving *)
(*    a B-quorum; Byzantine state actions may alter it arbitrarily for     *)
(*    Byzantine nodes.                                                     *)
(*                                                                         *)
(*  - sentMsg[src][dst] records that src has sent the protocol message to  *)
(*    dst.  Normal complete broadcasts set an entire outgoing row to TRUE; *)
(*    omission and Byzantine send actions may set only selected entries.   *)
(*    Sends are monotonic in the omission/Byzantine subset actions: once   *)
(*    an entry is TRUE, those actions preserve it.                         *)
(*                                                                         *)
(*  - rcvMsg[src][dst] records that dst has received src's message.  A     *)
(*    node relays after receiving an A-quorum and accepts after receiving  *)
(*    a B-quorum.  Byzantine state actions may arbitrarily rewrite a       *)
(*    Byzantine node's incoming receive column.                            *)
(***************************************************************************)

VARIABLES accept, sentMsg, rcvMsg

vars == << accept, sentMsg, rcvMsg >>

(***************************************************************************)
(* SentMsgProj(n) is the projection of sentMsg used in the Ivy model: it   *)
(* records whether n has sent its protocol message to at least one node.   *)
(***************************************************************************)

SentMsgProj(n) ==
  \E dst \in Node : sentMsg[n][dst]

(***************************************************************************)
(* HasAQuorumRcv(n, rm) means n has received messages from every member of *)
(* some A-quorum.  This is the relay threshold: after this condition holds *)
(* for a node, the normal protocol lets that node broadcast/relay.         *)
(***************************************************************************)

HasAQuorumRcv(n, rm) ==
  \E a \in QuorumA :
    \A src \in Node : InA(src, a) => rm[src][n]

(***************************************************************************)
(* HasBQuorumRcv(n, rm) means n has received messages from every member of *)
(* some B-quorum.  This is the acceptance threshold: after this condition  *)
(* holds for a node, the protocol lets that node accept the broadcast.     *)
(***************************************************************************)

HasBQuorumRcv(n, rm) ==
  \E b \in QuorumB :
    \A src \in Node : InB(src, b) => rm[src][n]

(***************************************************************************)
(* SendAllFrom(sm, n) returns a copy of the sent-message matrix sm where   *)
(* node n's whole outgoing row is TRUE.  It models a complete broadcast    *)
(* from n to every destination while preserving every other sender's row.  *)
(***************************************************************************)

SendAllFrom(sm, n) ==
  [src \in Node |->
    IF src = n THEN [dst \in Node |-> TRUE] ELSE sm[src]]

(***************************************************************************)
(* SetReceiveColumn(rm, n, col) returns a copy of the receive matrix rm    *)
(* where node n's incoming column is replaced by col.  It is used for      *)
(* Byzantine state changes that arbitrarily alter which messages n appears *)
(* to have received, without changing other nodes' receive state.          *)
(***************************************************************************)

SetReceiveColumn(rm, n, col) ==
  [src \in Node |->
    [dst \in Node |->
      IF dst = n THEN col[src] ELSE rm[src][dst]]]

(***************************************************************************)
(* Init starts with no accepted nodes, no sent messages, and no received   *)
(* messages.  RcvInit is static input, so it is a constant rather than     *)
(* initialized here.                                                       *)
(***************************************************************************)

Init ==
  /\ accept = [n \in Node |-> FALSE]
  /\ sentMsg = [src \in Node |-> [dst \in Node |-> FALSE]]
  /\ rcvMsg = [src \in Node |-> [dst \in Node |-> FALSE]]

(***************************************************************************)
(* ReceiveInit(n) models a normal node n receiving the initial broadcast   *)
(* input.  Once n has the input, it performs a complete broadcast: n's      *)
(* outgoing sentMsg row is set to TRUE for every destination.               *)
(***************************************************************************)

ReceiveInit(n) ==
  /\ n \in Node
  /\ n \in RcvInit
  /\ sentMsg' = SendAllFrom(sentMsg, n)
  /\ UNCHANGED << accept, rcvMsg >>

(***************************************************************************)
(* ReceiveMsg(n, s) is the normal receive/relay/accept transition.  If n   *)
(* receives s's message, it records rcvMsg[s][n].  If the updated receive  *)
(* matrix gives n a B-quorum, n accepts.  If it gives n an A-quorum, n     *)
(* relays by broadcasting to every destination.                             *)
(***************************************************************************)

ReceiveMsg(n, s) ==
  /\ n \in Node
  /\ s \in Node
  /\ sentMsg[s][n]
  /\ LET newRcv == [rcvMsg EXCEPT ![s][n] = TRUE] IN
       /\ rcvMsg' = newRcv
       /\ accept' =
            IF HasBQuorumRcv(n, newRcv)
              THEN [accept EXCEPT ![n] = TRUE]
              ELSE accept
       /\ sentMsg' =
            IF HasAQuorumRcv(n, newRcv)
              THEN SendAllFrom(sentMsg, n)
              ELSE sentMsg

(***************************************************************************)
(* ReceiveMsgC(n, s) is the receive transition for FaultC nodes.  These    *)
(* nodes are obedient, so receiving and accepting follow the normal rules. *)
(* Their omission fault appears only at relay time: after an A-quorum,     *)
(* send nondeterministically chooses whether n performs the full broadcast *)
(* or omits it completely.                                                 *)
(***************************************************************************)

ReceiveMsgC(n, s) ==
  /\ n \in FaultC
  /\ s \in Node
  /\ sentMsg[s][n]
  /\ \E send \in BOOLEAN :
       LET newRcv == [rcvMsg EXCEPT ![s][n] = TRUE] IN
         /\ rcvMsg' = newRcv
         /\ accept' =
              IF HasBQuorumRcv(n, newRcv)
                THEN [accept EXCEPT ![n] = TRUE]
                ELSE accept
         /\ sentMsg' =
              IF HasAQuorumRcv(n, newRcv) /\ send
                THEN SendAllFrom(sentMsg, n)
                ELSE sentMsg

(***************************************************************************)
(* ReceiveInitI(n) is the initial-send transition for FaultI nodes.  They  *)
(* are obedient but may omit asymmetrically, so the action chooses an       *)
(* arbitrary set of destinations while preserving every message n had      *)
(* already sent.                                                           *)
(***************************************************************************)

ReceiveInitI(n) ==
  /\ n \in FaultI
  /\ n \in RcvInit
  /\ \E newRow \in [Node -> BOOLEAN] :
       /\ \A dst \in Node : sentMsg[n][dst] => newRow[dst]
       /\ sentMsg' = [sentMsg EXCEPT ![n] = newRow]
  /\ UNCHANGED << accept, rcvMsg >>

(***************************************************************************)
(* ReceiveMsgI(n, s) is the receive transition for FaultI nodes.  Receipt  *)
(* and B-quorum acceptance are normal.  If an A-quorum would trigger relay, *)
(* n may send to any subset of destinations, again preserving prior sends. *)
(* If no A-quorum is present, n's outgoing row is unchanged.               *)
(***************************************************************************)

ReceiveMsgI(n, s) ==
  /\ n \in FaultI
  /\ s \in Node
  /\ sentMsg[s][n]
  /\ LET newRcv == [rcvMsg EXCEPT ![s][n] = TRUE] IN
       /\ rcvMsg' = newRcv
       /\ accept' =
            IF HasBQuorumRcv(n, newRcv)
              THEN [accept EXCEPT ![n] = TRUE]
              ELSE accept
       /\ \E newRow \in [Node -> BOOLEAN] :
            /\ IF HasAQuorumRcv(n, newRcv)
                 THEN \A dst \in Node : sentMsg[n][dst] => newRow[dst]
                 ELSE newRow = sentMsg[n]
            /\ sentMsg' = [sentMsg EXCEPT ![n] = newRow]

(***************************************************************************)
(* FaultySendS(n) models a symmetric Byzantine send.  A FaultS node may    *)
(* fabricate a broadcast, but because it is symmetric the send goes to     *)
(* every destination at once.                                              *)
(***************************************************************************)

FaultySendS(n) ==
  /\ n \in FaultS
  /\ sentMsg' = SendAllFrom(sentMsg, n)
  /\ UNCHANGED << accept, rcvMsg >>

(***************************************************************************)
(* FaultyStateSA(n) models arbitrary Byzantine local state for FaultS and  *)
(* FaultA nodes.  The node's accept bit and entire incoming receive column *)
(* may be rewritten nondeterministically.  Outgoing sent messages are not  *)
(* changed by this state-mutation action.                                  *)
(***************************************************************************)

FaultyStateSA(n) ==
  /\ n \in (FaultS \cup FaultA)
  /\ \E newAccept \in BOOLEAN :
     \E newCol \in [Node -> BOOLEAN] :
       /\ accept' = [accept EXCEPT ![n] = newAccept]
       /\ rcvMsg' = SetReceiveColumn(rcvMsg, n, newCol)
  /\ UNCHANGED sentMsg

(***************************************************************************)
(* FaultySendA(n) models arbitrary Byzantine sending.  A FaultA node may   *)
(* send inconsistently to any subset of destinations.  The chosen outgoing *)
(* row must be a superset of the old row, so messages already sent remain  *)
(* sent.                                                                   *)
(***************************************************************************)

FaultySendA(n) ==
  /\ n \in FaultA
  /\ \E newRow \in [Node -> BOOLEAN] :
       /\ \A dst \in Node : sentMsg[n][dst] => newRow[dst]
       /\ sentMsg' = [sentMsg EXCEPT ![n] = newRow]
  /\ UNCHANGED << accept, rcvMsg >>

Next ==
  \/ \E n \in Node : ReceiveInit(n)
  \/ \E n, s \in Node : ReceiveMsg(n, s)
  \/ \E n, s \in Node : ReceiveMsgC(n, s)
  \/ \E n \in Node : ReceiveInitI(n)
  \/ \E n, s \in Node : ReceiveMsgI(n, s)
  \/ \E n \in Node : FaultySendS(n)
  \/ \E n \in Node : FaultyStateSA(n)
  \/ \E n \in Node : FaultySendA(n)

CorrectReceiveInit(n) ==
  /\ Correct(n)
  /\ ReceiveInit(n)

CorrectReceiveMsg(n, s) ==
  /\ Correct(n)
  /\ ReceiveMsg(n, s)

SafetySpec ==
  /\ Init
  /\ [][Next]_vars

Spec ==
  /\ SafetySpec
  /\ \A n \in Node :
       (Correct(n) /\ n \in RcvInit) => WF_vars(CorrectReceiveInit(n))
  /\ \A n, s \in Node :
       Correct(n) => WF_vars(CorrectReceiveMsg(n, s))

Unforgeability ==
  (\E n \in Node : Obedient(n) /\ accept[n]) =>
  (\E m \in Node : Obedient(m) /\ m \in RcvInit)

THEOREM Safety == SafetySpec => []Unforgeability
  PROOF OMITTED

(***************************************************************************)
(* Temporal properties corresponding to Ivy's correctness and relay        *)
(* properties.  The explicit fairness premises in Ivy are represented here *)
(* by the fairness conjuncts in Spec.                                      *)
(***************************************************************************)

AllObedientInit ==
  \A n \in Node : Obedient(n) => n \in RcvInit

SomeCorrectAccepts ==
  \E n \in Node : Correct(n) /\ accept[n]

Correctness ==
  AllObedientInit => <>SomeCorrectAccepts

THEOREM CorrectnessLiveness == Spec => Correctness
  PROOF OMITTED

SomeObedientAccepts ==
  \E n \in Node : Obedient(n) /\ accept[n]

AllCorrectAccept ==
  \A n \in Node : Correct(n) => accept[n]

Relay ==
  <>SomeObedientAccepts => <>AllCorrectAccept

THEOREM RelayLiveness == Spec => Relay
  PROOF OMITTED

=============================================================================
