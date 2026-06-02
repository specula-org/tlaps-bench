---- MODULE tcp_proof_PrefixTwoNonEmpty ----
EXTENDS FiniteSetTheorems, FiniteSets, Integers, SequenceTheorems, Sequences, SequencesExt, SequencesExtTheorems, TLAPS
(* ---- Content from module tcp ---- *)
(* 
https://datatracker.ietf.org/doc/html/rfc9293

This spec abstracts from many details such as sequence numbers in RFC9293 and
focuses on the state transitions of the TCP finite state machine shown in the
diagram at the end of this file.
*)

CONSTANT 
    Peers

ASSUME PeersAssumption == Cardinality(Peers) = 2

States == {"LISTEN", "CLOSED", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED", 
          "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "CLOSE-WAIT", "LAST-ACK",
          "TIME-WAIT"}

VARIABLE
    tcb,
    connstate,
    network

vars == <<tcb, connstate, network>>

TypeOK ==
    /\ tcb \in [ Peers -> BOOLEAN ]
    /\ connstate \in [ Peers -> States ]
    /\ network \in [ Peers -> Seq({"SYN", "SYN,ACK", "ACK", "RST", "FIN"} \cup {"ACKofFIN"}) ]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

\* Action triggered by user commands:

PASSIVE_OPEN(local, remote) ==
    \* User command: PASSIVE-OPEN
    /\ local # remote
    /\ connstate[local] = "CLOSED"
    /\ UNCHANGED network
    /\ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
    /\ tcb' = [tcb EXCEPT ![local] = TRUE]

ACTIVE_OPEN(local, remote) ==
    \* User command: ACTIVE-OPEN
    /\ local # remote
    /\ connstate[local] = "CLOSED"
    /\ network' = [ network EXCEPT ![remote] = Append(@, "SYN")]
    /\ connstate' = [connstate EXCEPT ![local] = "SYN-SENT"]
    /\ tcb' = [tcb EXCEPT ![local] = TRUE]

CLOSE_SYN_SENT(local, remote) ==
    \* User command: CLOSE
    /\ local # remote
    /\ connstate[local] = "SYN-SENT"
    /\ UNCHANGED network
    /\ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]

CLOSE_SYN_RECEIVED(local, remote) ==
    \* User Command: CLOSE
    /\ local # remote
    /\ connstate[local] = "SYN-RECEIVED"
    /\ network' = [ network EXCEPT ![remote] = Append(@, "FIN")]
    /\ connstate' = [connstate EXCEPT ![local] = "FIN-WAIT-1"]
    /\ UNCHANGED tcb

SEND(local, remote) ==
    \* User command: SEND
    /\ local # remote
    /\ connstate[local] = "LISTEN"
    /\ network' = [ network EXCEPT ![remote] = Append(@, "SYN")]
    /\ connstate' = [connstate EXCEPT ![local] = "SYN-SENT"]
    /\ UNCHANGED tcb

CLOSE_LISTEN(local, remote) ==
    \* User command: CLOSE
    /\ local # remote
    /\ connstate[local] = "LISTEN"
    /\ UNCHANGED network
    /\ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]

CLOSE_ESTABLISHED(local, remote) ==
    \* User command: CLOSE
    /\ local # remote
    /\ connstate[local] = "ESTABLISHED"
    /\ network' = [ network EXCEPT ![remote] = Append(@, "FIN")]
    /\ connstate' = [connstate EXCEPT ![local] = "FIN-WAIT-1"]
    /\ UNCHANGED tcb

CLOSE_CLOSE_WAIT(local, remote) ==
    \* User command: CLOSE
    /\ local # remote
    /\ connstate[local] = "CLOSE-WAIT"
    /\ network' = [ network EXCEPT ![remote] = Append(@, "FIN")]
    /\ connstate' = [connstate EXCEPT ![local] = "LAST-ACK"]
    /\ UNCHANGED tcb

User ==
    \E local, remote \in Peers :
        \/ ACTIVE_OPEN(local, remote)
        \/ PASSIVE_OPEN(local, remote)
        \/ CLOSE_SYN_SENT(local, remote)
        \/ CLOSE_SYN_RECEIVED(local, remote)
        \/ CLOSE_LISTEN(local, remote)
        \/ CLOSE_ESTABLISHED(local, remote)
        \/ CLOSE_CLOSE_WAIT(local, remote)
        \/ SEND(local, remote)

-----------------------------------------------------------------------------
       
SynSent(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "SYN-SENT"
    /\ UNCHANGED tcb
    /\ \/ /\ IsPrefix(<<"SYN">>, network[local])
          /\ network' = [ network EXCEPT ![remote] = Append(@, "SYN,ACK"),
                                         ![local] = Tail(network[local])]
          /\ connstate' = [connstate EXCEPT ![local] = "SYN-RECEIVED"]
       \/ /\ IsPrefix(<<"SYN,ACK">>, network[local])
          /\ network' = [ network EXCEPT ![remote] = Append(@, "ACK"),
                                         ![local] = Tail(network[local])]
          /\ connstate' = [connstate EXCEPT ![local] = "ESTABLISHED"]

SynReceived(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "SYN-RECEIVED"
    /\ UNCHANGED tcb
    /\ \/ /\ IsPrefix(<<"RST">>, network[local]) \* TODO: note 1 in RFC 9293 (must have gotten here from a *passive* OPEN, i.e., LISTEN)
          /\ network' = [ network EXCEPT ![local] = Tail(network[local])]
          /\ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
       \/ /\ IsPrefix(<<"ACK">>, network[local]) \* TODO: ACK of SYN
          /\ network' = [ network EXCEPT ![local] = Tail(network[local])]
          /\ connstate' = [connstate EXCEPT ![local] = "ESTABLISHED"]

Listen(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "LISTEN"
    /\ UNCHANGED tcb
    /\ \/ /\ IsPrefix(<<"SYN">>, network[local])
          /\ network' = [ network EXCEPT ![remote] = Append(@, "SYN,ACK"),
                                         ![local] = Tail(network[local])]
          /\ connstate' = [connstate EXCEPT ![local] = "SYN-RECEIVED"]

Established(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "ESTABLISHED"
    /\ UNCHANGED tcb
    /\ IsPrefix(<<"FIN">>, network[local])
    /\ network' = [ network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                   ![local] = Tail(network[local])]
    /\ connstate' = [connstate EXCEPT ![local] = "CLOSE-WAIT"]

-----------------------------------------------------------------------------

FinWait1(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "FIN-WAIT-1"
    /\ UNCHANGED tcb
    /\ \/ /\ IsPrefix(<<"FIN">>, network[local])
          /\ network' = [ network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                         ![local] = Tail(network[local])]
          /\ connstate' = [connstate EXCEPT ![local] = "CLOSING"]
       \/ /\ IsPrefix(<<"ACKofFIN">>, network[local])
          /\ network' = [ network EXCEPT ![local] = Tail(network[local])]
          /\ connstate' = [connstate EXCEPT ![local] = "FIN-WAIT-2"]

FinWait2(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "FIN-WAIT-2"
    /\ UNCHANGED tcb
    /\ IsPrefix(<<"FIN">>, network[local])
    /\ network' = [ network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                   ![local] = Tail(network[local])]
    /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]

Closing(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "CLOSING"
    /\ UNCHANGED tcb
    /\ IsPrefix(<<"ACKofFIN">>, network[local])
    /\ network' = [ network EXCEPT ![local] = Tail(network[local])]
    /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]

LastAck(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "LAST-ACK"
    /\ UNCHANGED tcb
    /\ IsPrefix(<<"ACKofFIN">>, network[local])
    /\ network' = [ network EXCEPT ![local] = Tail(network[local])]
    /\ connstate' = [connstate EXCEPT ![local] = "CLOSED"]

TimeWait(local, remote) ==
    /\ local # remote
    /\ connstate[local] = "TIME-WAIT"
    /\ tcb[local]
    /\ UNCHANGED network
    /\ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    \* TODO: Timeout=2MSL

Note2(local, remote) ==
    (* Note 2: A transition from FIN-WAIT-1 to TIME-WAIT if a FIN is received
       and the local FIN is also acknowledged. *)
    /\ local # remote
    /\ connstate[local] = "FIN-WAIT-1"
    /\ UNCHANGED tcb
    \* The local FIN is also acknowledged, i.e., skipping the CLOSING state.
    /\ IsPrefix(<< "FIN", "ACKofFIN" >>, network[local])
    \* ??? The RFC doesn't explictly mention this, but we send the ACKofFIN here.
    /\ network' = [ network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                   ![local] = SubSeq(network[local], 3, Len(network[local]))]
    /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]

System ==
    \E local, remote \in Peers :
        \/ SynSent(local, remote)
        \/ SynReceived(local, remote)
        \/ Listen(local, remote)
        \/ Established(local, remote)
        \/ FinWait1(local, remote)
        \/ FinWait2(local, remote)
        \/ Closing(local, remote)
        \/ LastAck(local, remote)
        \/ TimeWait(local, remote)
        \/ Note2(local, remote)

Note3(local, remote) ==
    (* Note 3: A RST can be sent from any state with a corresponding transition 
       to TIME-WAIT (see [70] for rationale). Similarly, receipt of a RST from
       any state results in a transition to LISTEN or CLOSED. *)
    \* ??? "...can be sent from any state with a corresponding transition to TIME-WAIT"
    \* ??? could also be interpreted as those states from where we can tranisiton to TIME-WAIT,
    \* ??? i.e., FIN-WAIT-1, FIN-WAIT-2, CLOSING.
    /\ local # remote
    /\ UNCHANGED tcb
    /\ \/ /\ tcb[local] \* ??? RFC 9293 doesn't mention this, but it seems impossible to send a RST without a TCB.
          /\ network' = [ network EXCEPT ![remote] = Append(@, "RST")]
          /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]
       \/ /\ IsPrefix(<<"RST">>, network[local])
          /\ network' = [ network EXCEPT ![local] = Tail(network[local])]
          /\ \/ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
             \/ connstate' = [connstate EXCEPT ![local] = "CLOSED"]

Reset ==
    \E local, remote \in Peers :
        Note3(local, remote)

Next ==
    \/ System
    \/ Reset
    \/ User

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(System)
    \* Would get stuck in SYN-SENT if we don't assert a user command.
    /\ WF_vars(\E local, remote \in Peers: CLOSE_SYN_SENT(local, remote))

-----------------------------------------------------------------------------

Inv ==
    \* If there are no messages in flight and one node is in the ESTABLISHED
    \* state, then the other node is also in the ESTABLISHED state. When
    \* message are in flight, the state of the nodes can be different.
    \A local, remote \in { p \in Peers : network[p] = <<>> } :
        connstate[local] = "ESTABLISHED" <=> connstate[remote] = "ESTABLISHED"

Prop ==
    \A p \in Peers :
        connstate[p] = "SYN-SENT" ~> connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}


(***************************************************************************)
(* TLAPS proofs for the TCP FSM specification:                             *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []Inv  (ESTABLISHED agreement when both networks are empty)   *)
(***************************************************************************)

\* The spec's `ASSUME PeersAssumption == Cardinality(Peers) = 2` is intended
\* to assert that Peers is a finite set with exactly two elements.  In TLA+,
\* Cardinality is defined via CHOOSE and may return arbitrary values for
\* infinite sets, so we add the natural finiteness witness here.
ASSUME PeersFinite == IsFiniteSet(Peers)

(***************************************************************************)
(* The set of network messages used by the spec.                           *)
(***************************************************************************)
Msgs == {"SYN", "SYN,ACK", "ACK", "RST", "FIN", "ACKofFIN"}

LEMMA NetworkType ==
  TypeOK <=> /\ tcb \in [Peers -> BOOLEAN]
             /\ connstate \in [Peers -> States]
             /\ network \in [Peers -> Seq(Msgs)]
  PROOF OMITTED

LEMMA TailIsSeq ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Tail(s) \in Seq(T)
  OBVIOUS

LEMMA AppendInSeq ==
  ASSUME NEW T, NEW s \in Seq(T), NEW e \in T
  PROVE  Append(s, e) \in Seq(T)
  OBVIOUS

(***************************************************************************)
(* IsPrefix with a non-empty argument forces the second sequence to be     *)
(* non-empty.  We use the unfolded definition to avoid a fragile           *)
(* dependency on the longer Theorems.                                      *)
(***************************************************************************)
LEMMA PrefixOneNonEmpty ==
  ASSUME NEW T, NEW e \in T, NEW s \in Seq(T), IsPrefix(<<e>>, s)
  PROVE  /\ s # << >>
         /\ Head(s) = e
         /\ Tail(s) \in Seq(T)
  PROOF OMITTED

LEMMA PrefixTwoNonEmpty ==
  ASSUME NEW T, NEW e1 \in T, NEW e2 \in T, NEW s \in Seq(T),
         IsPrefix(<<e1, e2>>, s)
  PROVE  /\ Len(s) >= 2
         /\ s[1] = e1
         /\ s[2] = e2
PROOF OBVIOUS

========================================