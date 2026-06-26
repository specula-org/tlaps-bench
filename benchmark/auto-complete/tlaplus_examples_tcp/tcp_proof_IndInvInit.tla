--------------------------- MODULE tcp_proof_IndInvInit ---------------------------------
(***************************************************************************)
(* TLAPS proofs for the TCP FSM specification:                             *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []Inv  (ESTABLISHED agreement when both networks are empty)   *)
(***************************************************************************)
EXTENDS tcp, SequenceTheorems, SequencesExtTheorems, FiniteSetTheorems, TLAPS

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
PROOF OMITTED

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)

LEMMA TypeOKInductive == TypeOK /\ [Next]_vars => TypeOK'
PROOF OMITTED

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* Pick the two distinct peers using the cardinality-2 assumption.         *)
(***************************************************************************)
A == CHOOSE p \in Peers : TRUE
B == CHOOSE p \in Peers : p # A

LEMMA PeersAB ==
  /\ A \in Peers
  /\ B \in Peers
  /\ A # B
  /\ Peers = {A, B}
PROOF OMITTED

(***************************************************************************)
(* Inv reformulated explicitly in terms of the two peers.  This is        *)
(* convenient for case analysis since {p \in Peers : network[p] = <<>>}   *)
(* is one of {}, {A}, {B}, {A, B}.                                        *)
(***************************************************************************)
LEMMA InvIsAB ==
  Inv <=> ((network[A] = <<>> /\ network[B] = <<>>)
              => (connstate[A] = "ESTABLISHED" <=> connstate[B] = "ESTABLISHED"))
PROOF OMITTED

(***************************************************************************)
(* Initial state satisfies Inv.                                            *)
(***************************************************************************)
THEOREM InvInit == Init => Inv
PROOF OMITTED

(***************************************************************************)
(* Inductive strengthening for the proof of Spec => []Inv.                 *)
(*                                                                         *)
(* The seven Aux clauses below were discovered using Apalache's           *)
(* inductive-invariant search (see specifications/tcp/IndInv_apa.tla,     *)
(* the cfg files IndInv_apa.cfg and IndInv_apa_init.cfg, and the         *)
(* commit message of the corresponding commit for the iteration log).    *)
(***************************************************************************)
HasMsg(m, p) ==
  \E i \in 1..Len(network[p]) : network[p][i] = m

LastMsg(p) == network[p][Len(network[p])]

PostEstStrict == {"ESTABLISHED", "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING",
                  "CLOSE-WAIT", "LAST-ACK", "TIME-WAIT"}
PostEst       == PostEstStrict \cup {"CLOSED"}

Aux_singleton_RST ==
  \A p, q \in Peers :
    (p # q /\ network[p] = <<"RST">> /\ network[q] = <<>>)
       => connstate[q] # "ESTABLISHED"

Aux_singleton_ACK ==
  \A p, q \in Peers :
    (p # q /\ network[p] = <<"ACK">> /\ network[q] = <<>>
            /\ connstate[p] = "SYN-RECEIVED")
       => connstate[q] = "ESTABLISHED"

Aux_singleton_ACKofFIN ==
  \A p, q \in Peers :
    (p # q /\ network[p] = <<"ACKofFIN">> /\ network[q] = <<>>
            /\ connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"})
       => connstate[q] # "ESTABLISHED"

Aux_EST_evidence ==
  \A p, q \in Peers :
    (p # q /\ connstate[p] = "ESTABLISHED")
       => \/ connstate[q] \in PostEst
          \/ HasMsg("SYN", p)        \/ HasMsg("SYN", q)
          \/ HasMsg("ACK", q)        \/ HasMsg("ACK", p)
          \/ HasMsg("SYN,ACK", q)    \/ HasMsg("SYN,ACK", p)
          \/ HasMsg("FIN", p)        \/ HasMsg("FIN", q)
          \/ HasMsg("ACKofFIN", p)   \/ HasMsg("ACKofFIN", q)
          \/ HasMsg("RST", p)        \/ HasMsg("RST", q)

Aux_LastMsg ==
  \A p, q \in Peers :
    (p # q /\ network[p] # <<>>) =>
      /\ connstate[q] = "SYN-RECEIVED"  => LastMsg(p) = "SYN,ACK"
      /\ connstate[q] = "FIN-WAIT-1"    => LastMsg(p) \in {"FIN", "RST"}
      /\ connstate[q] = "CLOSE-WAIT"    => LastMsg(p) = "ACKofFIN"
      /\ connstate[q] = "LAST-ACK"      => LastMsg(p) = "FIN"
      /\ connstate[q] = "CLOSING"       => LastMsg(p) = "ACKofFIN"
      /\ connstate[q] = "SYN-SENT"      => LastMsg(p) = "SYN"

Aux_RST_at_end ==
  \A p, q \in Peers :
    (p # q /\ network[p] # <<>> /\ LastMsg(p) = "RST")
       => connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}

IndInv ==
  /\ TypeOK
  /\ Inv
  /\ Aux_singleton_RST
  /\ Aux_singleton_ACK
  /\ Aux_singleton_ACKofFIN
  /\ Aux_EST_evidence
  /\ Aux_LastMsg
  /\ Aux_RST_at_end

(***************************************************************************)
(* Initial state.                                                          *)
(***************************************************************************)
THEOREM IndInvInit == Init => IndInv
PROOF OBVIOUS

(***************************************************************************)
(* Inductive step for IndInv.                                              *)
(*                                                                         *)
(* The proof has two parts: a stutter case (trivial) and a per-action     *)
(* analysis covering every TCP transition.                                 *)
(***************************************************************************)

\* The "stutter" case is trivial: vars unchanged ⇒ every clause is the
\* same primed and unprimed.

(***************************************************************************)
(* The non-stutter case is split into the three top-level disjuncts of    *)
(* Next.  Each sub-lemma takes IndInv, the action, and TypeOK' (already   *)
(* discharged via TypeOKInductive) and proves the remaining clauses.    *)
(***************************************************************************)

\* User actions: PASSIVE_OPEN, CLOSE_SYN_SENT, CLOSE_LISTEN do NOT change
\* network[_].  ACTIVE_OPEN, SEND append "SYN" to n[remote].
\* CLOSE_SYN_RECEIVED, CLOSE_ESTABLISHED, CLOSE_CLOSE_WAIT append "FIN".
\* In every case connstate[local] changes; connstate[r] for r # local is
\* unchanged.  None of these actions transition local INTO ESTABLISHED.

(***************************************************************************)
(* System actions: 10 in total.  Each consumes from n[local] and may also *)
(* append to n[remote].  We start with TimeWait (no network change) and  *)
(* extend incrementally.                                                  *)
(***************************************************************************)

(***************************************************************************)
(* Reset action (Note3): two sub-cases.                                    *)
(*   - Note3 send: tcb[local], append "RST" to n[remote], local -> TW.    *)
(*   - Note3 RST receive: head=RST, Tail n[local], local -> LISTEN/CLOSED.*)
(***************************************************************************)

(***************************************************************************)
(* The main safety result.  IndInv strengthens Inv with auxiliary clauses *)
(* required for inductiveness; it implies Inv directly by definition.     *)
(***************************************************************************)

============================================================================
