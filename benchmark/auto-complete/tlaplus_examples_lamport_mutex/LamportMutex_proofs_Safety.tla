------------------------ MODULE LamportMutex_proofs_Safety -------------------------
(***************************************************************************)
(* Proof of type correctness and safety of Lamport's distributed           *)
(* mutual-exclusion algorithm.                                             *)
(***************************************************************************)
EXTENDS LamportMutex, SequenceTheorems, TLAPS

USE DEF Clock

(***************************************************************************)
(* Proof of type correctness.                                              *)
(***************************************************************************)
LEMMA BroadcastType ==
  ASSUME network \in [Proc -> [Proc -> Seq(Message)]],
         NEW s \in Proc, NEW m \in Message
  PROVE  Broadcast(s,m) \in [Proc -> Seq(Message)]
PROOF OMITTED

LEMMA TypeCorrect == Spec => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* Inductive invariants for the algorithm.                                 *)
(***************************************************************************)

(***************************************************************************)
(* We start the proof of safety by defining some auxiliary predicates:     *)
(* - Contains(s,mt) holds if channel s contains a message of type mt.      *)
(* - AtMostOne(s,mt) holds if channel s holds zero or one messages of      *)
(*   type mtype.                                                           *)
(* - Precedes(s,mt1,mt2) holds if in channel s, any message of type mt1    *)
(*   precedes any message of type mt2.                                     *)
(***************************************************************************)
Contains(s,mtype) == \E i \in 1 .. Len(s) : s[i].type = mtype
AtMostOne(s,mtype) == \A i,j \in 1 .. Len(s) :
  s[i].type = mtype /\ s[j].type = mtype => i = j
Precedes(s,mt1,mt2) == \A i,j \in 1 .. Len(s) :
  s[i].type = mt1 /\ s[j].type = mt2 => i < j

LEMMA NotContainsAtMostOne ==
  ASSUME NEW s \in Seq(Message), NEW mtype, ~ Contains(s,mtype)
  PROVE  AtMostOne(s, mtype)
PROOF OMITTED

LEMMA NotContainsPrecedes ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2, ~ Contains(s, mt2)
  PROVE  /\ Precedes(s, mt1, mt2)
         /\ Precedes(s, mt2, mt1)
PROOF OMITTED

LEMMA PrecedesHead ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2,
         s # << >>,
         Precedes(s,mt1,mt2), Head(s).type = mt2
  PROVE  ~ Contains(s,mt1)
PROOF OMITTED

LEMMA AtMostOneTail ==
  ASSUME NEW s \in Seq(Message), NEW mtype,
         s # << >>, AtMostOne(s, mtype)
  PROVE  AtMostOne(Tail(s), mtype)
PROOF OMITTED

LEMMA ContainsTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mtype, AtMostOne(s, mtype)
  PROVE  Contains(Tail(s), mtype) <=> Contains(s, mtype) /\ Head(s).type # mtype
PROOF OMITTED

LEMMA AtMostOneHead ==
  ASSUME NEW s \in Seq(Message), NEW mtype,
         AtMostOne(s,mtype), s # << >>, Head(s).type = mtype
  PROVE  ~ Contains(Tail(s), mtype)
PROOF OMITTED

LEMMA ContainsSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, NEW m \in Message
  PROVE  Contains(Append(s,m), mtype) <=> m.type = mtype \/ Contains(s, mtype)
PROOF OMITTED

LEMMA NotContainsSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, ~ Contains(s, mtype), NEW m \in Message
  PROVE  /\ AtMostOne(Append(s,m), mtype)
         /\ m.type # mtype => ~ Contains(Append(s,m), mtype)
PROOF OMITTED

LEMMA AtMostOneSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, AtMostOne(s, mtype), 
         NEW m \in Message, m.type # mtype
  PROVE  AtMostOne(Append(s,m), mtype)
PROOF OMITTED

LEMMA PrecedesSend ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2,
         NEW m \in Message, m.type # mt1
  PROVE  Precedes(Append(s,m), mt1, mt2) <=> Precedes(s, mt1, mt2)
PROOF OMITTED

LEMMA PrecedesTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mt1, NEW mt2, Precedes(s, mt1, mt2)
  PROVE  Precedes(Tail(s), mt1, mt2)
PROOF OMITTED

LEMMA PrecedesInTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mt1, NEW mt2, mt1 # mt2,
         Head(s).type = mt1 \/ Head(s).type \notin {mt1, mt2},
         Precedes(Tail(s), mt1, mt2)
  PROVE  Precedes(s, mt1, mt2)
PROOF OMITTED

(***************************************************************************)
(* In order to prove the safety property of the algorithm, we prove two    *)
(* inductive invariants. Our first invariant is itself a conjunction of    *)
(* two predicates:                                                         *)
(* - The first one states that each channel holds at most one message of   *)
(*   each type. Moreover, no process ever sends a message to itself.       *)
(* - The second predicate describes how request, acknowledgement, and      *)
(*   release messages are exchanged among processes, but does not refer to *)
(*   clock values held in the clock and req variables.                     *)
(***************************************************************************)

NetworkInv(p,q) ==
  LET s == network[p][q]
  IN  /\ AtMostOne(s,"req")
      /\ AtMostOne(s,"ack")
      /\ AtMostOne(s,"rel")
      /\ network[p][p] = << >>

CommInv(p) ==
  \/ /\ req[p][p] = 0 /\ ack[p] = {} /\ p \notin crit
     /\ \A q \in Proc : ~ Contains(network[p][q],"req") /\ ~ Contains(network[q][p],"ack")
  \/ /\ req[p][p] > 0 /\ p \in ack[p]
     /\ p \in crit => ack[p] = Proc
     /\ \A q \in Proc :
           LET pq == network[p][q]
               qp == network[q][p]
           IN  \/ /\ q \in ack[p]
                  /\ ~ Contains(pq,"req") /\ ~ Contains(qp,"ack") /\ ~ Contains(pq,"rel")
               \/ /\ q \notin ack[p] /\ Contains(qp,"ack")
                  /\ ~ Contains(pq,"req") /\ ~ Contains(pq,"rel")
               \/ /\ q \notin ack[p] /\ Contains(pq,"req")
                  /\ ~ Contains(qp,"ack") /\ Precedes(pq,"rel","req")

BasicInv == 
  /\ \A p,q \in Proc : NetworkInv(p,q)
  /\ \A p \in Proc : CommInv(p)

THEOREM BasicInvariant == Spec => []BasicInv
PROOF OMITTED

(***************************************************************************)
(* The second invariant relates the clock values stored in the clock and   *)
(* req variables, as well as in request messages. Its proof relies on the  *)
(* "basic" invariant proved previously.                                    *)
(***************************************************************************)

ClockInvInner(p,q) ==
  LET pq == network[p][q]
      qp == network[q][p]
  IN  /\ \A i \in 1 .. Len(pq) : pq[i].type = "req" => pq[i].clock = req[p][p]
      /\ Contains(qp, "ack") \/ q \in ack[p] => 
             /\ req[q][p] = req[p][p]
             /\ clock[q] > req[p][p]
             /\ Precedes(qp, "ack", "req") =>
                  \A i \in 1 .. Len(qp) : qp[i].type = "req" => qp[i].clock > req[p][p]
      /\ p \in crit => beats(p,q)

ClockInv == \A p \in Proc : \A q \in Proc \ {p} : ClockInvInner(p,q)

THEOREM ClockInvariant == Spec => []ClockInv
PROOF OMITTED

(***************************************************************************)
(* Mutual exclusion is a simple consequence of the above invariants.       *)
(* In particular, if two distinct processes p and q were ever in the       *)
(* critical section at the same instant, then beats(p,q) and beats(q,p)    *)
(* would both have to hold, but this is impossible.                        *)
(***************************************************************************)
THEOREM Safety == Spec => []Mutex
PROOF OBVIOUS

(***************************************************************************)
(* Bounded channels: no channel ever holds more than 3 messages.  This is *)
(* a corollary of the AtMostOne fact for each of the three message types  *)
(* in NetworkInv: with three possible types and at most one of each, a    *)
(* well-typed channel has at most three messages.                         *)
(***************************************************************************)

==============================================================================
