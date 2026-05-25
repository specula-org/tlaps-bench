------------------------------- MODULE PaxosHistVar_Invariant --------------------------
(*
Basic Paxos verified using only history variables.

See https://github.com/sachand/HistVar/blob/master/Basic%20Paxos/PaxosUs.tla
*)
EXTENDS Integers, TLAPS, NaturalsInduction

CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == Nat

VARIABLES sent

vars == <<sent>>

Send(m) == sent' = sent \cup {m}

None == CHOOSE v : v \notin Values

Init == sent = {}

(***************************************************************************)
(* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
(* with ballot b to a majority of acceptors.  It can do this only if it    *)
(* has not already sent a 1a message for ballot b.                         *)
(***************************************************************************)
Phase1a(b) == Send([type |-> "1a", bal |-> b])
              
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b and with the highest-numbered ballot   *)
(* (if any) for which it has voted for a value and the value it voted for  *)
(* in that ballot.  That promise is made in a 1b message.                  *)
(***************************************************************************)
last_voted(a) == LET 2bs == {m \in sent: m.type = "2b" /\ m.acc = a}
                 IN IF 2bs # {} THEN {m \in 2bs: \A m2 \in 2bs: m.bal >= m2.bal}
                    ELSE {[bal |-> -1, val |-> None]}

Phase1b(a) ==
  \E m \in sent, r \in last_voted(a):
     /\ m.type = "1a"
     /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal > m2.bal
     /\ Send([type |-> "1b", bal |-> m.bal,
              maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a])
        
(***************************************************************************)
(* Phase 2a: If the leader receives a response to its 1b message (for      *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b with a value v, where v is the     *)
(* value of the highest-numbered proposal among the responses, or is any   *)
(* value if the responses reported no proposals.  The leader can send only *)
(* one 2a message for any ballot.                                          *)
(***************************************************************************)
Phase2a(b) ==
  /\ ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b) 
  /\ \E v \in Values, Q \in Quorums, S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = b}:
       /\ \A a \in Q : \E m \in S : m.acc = a
       /\ \/ \A m \in S : m.maxVBal = -1
          \/ \E c \in 0..(b-1) : 
               /\ \A m \in S : m.maxVBal =< c
               /\ \E m \in S : /\ m.maxVBal = c
                               /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot numbered    *)
(* b, it votes for the message's value in ballot b unless it has already   *)
(* responded to a 1a request for a ballot number greater than or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
Phase2b(a) == 
  \E m \in sent :
    /\ m.type = "2a" 
    /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal >= m2.bal
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])

Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a) 

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  Wnat it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(v) means that v  *)
(* has been chosen.  From this definition, it is obvious how a process     *)
(* learns that a value has been chosen from messages of type "2b".         *)
(***************************************************************************)
VotedForIn(a, v, b) == \E m \in sent : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
-----------------------------------------------------------------------------
(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK == sent \in SUBSET Messages

(***************************************************************************)
(* WontVoteIn(a, b) is a predicate that implies that a has not voted and   *)
(* never will vote in ballot b.                                            *)
(***************************************************************************)                                       
WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ \E m \in sent: m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b

(***************************************************************************)
(* The predicate SafeAt(v, b) implies that no value other than perhaps v   *)
(* has been or ever will be chosen in any ballot numbered less than b.     *)
(***************************************************************************)                   
SafeAt(v, b) == 
  \A b2 \in 0..(b-1) :
    \E Q \in Quorums :
      \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)

MsgInv ==
  \A m \in sent : 
    /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                        /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
    /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                        /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
    /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                         /\ m2.bal  = m.bal
                                         /\ m2.val  = m.val

Inv == TypeOK /\ MsgInv

(***************************************************************************)
(* The following two lemmas are simple consequences of the definitions.    *)
(***************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b) is stable, meaning that once it becomes true, it *)
(* remains true throughout the rest of the excecution.                     *)
(***************************************************************************)

(***************************************************************************)
(* Per-message invariant predicate: MsgInv is the conjunction over all     *)
(* messages of MsgInvFor.                                                   *)
(***************************************************************************)
MsgInvFor(m) ==
    /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                        /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
    /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                        /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
    /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                         /\ m2.bal  = m.bal
                                         /\ m2.val  = m.val

LEMMA MsgInvEquiv == MsgInv <=> \A m \in sent : MsgInvFor(m)
BY DEF MsgInv, MsgInvFor

(***************************************************************************)
(* Helper lemmas about VotedForIn, SafeAt and WontVoteIn under the growth  *)
(* of the set `sent`.                                                      *)
(***************************************************************************)

LEMMA VotedForInMonotone ==
  ASSUME NEW aa, NEW vv, NEW bb, NEW mm, sent' = sent \cup {mm},
         VotedForIn(aa, vv, bb)
  PROVE  VotedForIn(aa, vv, bb)'
BY DEF VotedForIn

LEMMA NoVoteNon2b ==
  ASSUME NEW aa, NEW vv, NEW bb, NEW mm, sent' = sent \cup {mm}, mm.type # "2b"
  PROVE  VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
BY DEF VotedForIn

LEMMA NoVoteOtherBal ==
  ASSUME NEW aa, NEW vv, NEW bb, NEW mm, sent' = sent \cup {mm}, mm.bal # bb,
         VotedForIn(aa, vv, bb)'
  PROVE  VotedForIn(aa, vv, bb)
BY DEF VotedForIn

LEMMA NoVoteOtherAcc ==
  ASSUME NEW aa, NEW vv, NEW bb, NEW mm, sent' = sent \cup {mm}, mm.acc # aa,
         VotedForIn(aa, vv, bb)'
  PROVE  VotedForIn(aa, vv, bb)
BY DEF VotedForIn

LEMMA NoNewVoteGen ==
  ASSUME NEW aa, NEW vv, NEW bb, NEW mm, sent' = sent \cup {mm},
         ~(mm.type = "2b" /\ mm.acc = aa /\ mm.bal = bb),
         VotedForIn(aa, vv, bb)'
  PROVE  VotedForIn(aa, vv, bb)
<1>1. PICK m \in sent' : m.type = "2b" /\ m.val = vv /\ m.bal = bb /\ m.acc = aa
      BY DEF VotedForIn
<1>2. m # mm BY <1>1
<1>3. m \in sent BY <1>1, <1>2
<1> QED BY <1>1, <1>3 DEF VotedForIn

LEMMA WontVoteInPreserved ==
  ASSUME NEW aa, NEW bb, NEW mm, sent' = sent \cup {mm},
         WontVoteIn(aa, bb),
         ~(mm.type = "2b" /\ mm.acc = aa /\ mm.bal = bb)
  PROVE  WontVoteIn(aa, bb)'
<1>1. \A v \in Values : ~ VotedForIn(aa, v, bb)'
  <2> SUFFICES ASSUME NEW v \in Values, VotedForIn(aa, v, bb)' PROVE FALSE OBVIOUS
  <2>1. PICK m \in sent' : m.type = "2b" /\ m.val = v /\ m.bal = bb /\ m.acc = aa
        BY DEF VotedForIn
  <2>2. m # mm BY <2>1
  <2>3. m \in sent BY <2>1, <2>2
  <2>4. VotedForIn(aa, v, bb) BY <2>1, <2>3 DEF VotedForIn
  <2> QED BY <2>4 DEF WontVoteIn
<1>2. \E m \in sent' : m.type \in {"1b", "2b"} /\ m.acc = aa /\ m.bal > bb
  BY DEF WontVoteIn
<1> QED BY <1>1, <1>2 DEF WontVoteIn

LEMMA SafeAtStableNon2b ==
  ASSUME NEW v, NEW b, NEW mm, sent' = sent \cup {mm}, mm.type # "2b",
         SafeAt(v, b)
  PROVE  SafeAt(v, b)'
<1> SUFFICES ASSUME NEW b2 \in 0..(b-1)
             PROVE  \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
    BY DEF SafeAt
<1>1. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
      BY DEF SafeAt
<1>2. \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
  <2> TAKE a \in Q
  <2>1. VotedForIn(a, v, b2) \/ WontVoteIn(a, b2) BY <1>1
  <2>2. CASE VotedForIn(a, v, b2)
        BY <2>2, VotedForInMonotone
  <2>3. CASE WontVoteIn(a, b2)
        BY <2>3, WontVoteInPreserved
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>2

LEMMA SafeAtStableVote ==
  ASSUME NEW v, NEW b, NEW mm, TypeOK, sent' = sent \cup {mm}, mm.type = "2b",
         \A m2 \in sent : m2.type \in {"1b", "2b"} /\ m2.acc = mm.acc => mm.bal >= m2.bal,
         SafeAt(v, b)
  PROVE  SafeAt(v, b)'
<1> SUFFICES ASSUME NEW b2 \in 0..(b-1)
             PROVE  \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
    BY DEF SafeAt
<1>1. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
      BY DEF SafeAt
<1>2. \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
  <2> TAKE a \in Q
  <2>1. VotedForIn(a, v, b2) \/ WontVoteIn(a, b2) BY <1>1
  <2>2. CASE VotedForIn(a, v, b2)
        BY <2>2, VotedForInMonotone
  <2>3. CASE WontVoteIn(a, b2)
    <3>1. ~(mm.type = "2b" /\ mm.acc = a /\ mm.bal = b2)
      <4> SUFFICES ASSUME mm.acc = a, mm.bal = b2 PROVE FALSE OBVIOUS
      <4>1. PICK mw \in sent : mw.type \in {"1b", "2b"} /\ mw.acc = a /\ mw.bal > b2
            BY <2>3 DEF WontVoteIn
      <4>2. mw.acc = mm.acc BY <4>1
      <4>3. mm.bal >= mw.bal BY <4>1, <4>2
      <4>4. mw.bal \in Int BY <4>1, TypeOK DEF TypeOK, Messages, Ballots
      <4> QED BY <4>1, <4>3, <4>4
    <3>2. WontVoteIn(a, b2)' BY <2>3, <3>1, WontVoteInPreserved
    <3> QED BY <3>2
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>2

LEMMA VotedOnce ==
  MsgInv => \A a1, a2, bb, v1, v2 :
              VotedForIn(a1, v1, bb) /\ VotedForIn(a2, v2, bb) => (v1 = v2)
<1> SUFFICES ASSUME MsgInv, NEW a1, NEW a2, NEW bb, NEW v1, NEW v2,
                    VotedForIn(a1, v1, bb), VotedForIn(a2, v2, bb)
             PROVE  v1 = v2
    OBVIOUS
<1>1. PICK m1 \in sent : m1.type = "2b" /\ m1.val = v1 /\ m1.bal = bb /\ m1.acc = a1
      BY DEF VotedForIn
<1>2. PICK m2 \in sent : m2.type = "2b" /\ m2.val = v2 /\ m2.bal = bb /\ m2.acc = a2
      BY DEF VotedForIn
<1>3. PICK ma1 \in sent : ma1.type = "2a" /\ ma1.bal = bb /\ ma1.val = v1
      BY <1>1, MsgInv DEF MsgInv
<1>4. PICK ma2 \in sent : ma2.type = "2a" /\ ma2.bal = bb /\ ma2.val = v2
      BY <1>2, MsgInv DEF MsgInv
<1>5. ma2 = ma1 BY <1>3, <1>4, MsgInv DEF MsgInv
<1> QED BY <1>3, <1>4, <1>5

(***************************************************************************)
(* Preservation of the per-message invariant for old messages, when the    *)
(* added message is not a vote ("2b").                                      *)
(***************************************************************************)
LEMMA OldPreservedNon2b ==
  ASSUME NEW mm, TypeOK, MsgInv, sent' = sent \cup {mm}, mm.type # "2b",
         mm.type = "2a" => ~\E mu \in sent : mu.type = "2a" /\ mu.bal = mm.bal,
         NEW m \in sent
  PROVE  MsgInvFor(m)'
<1>0. MsgInvFor(m) BY DEF MsgInv, MsgInvFor
<1>1. m.type = "1b" => (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
                       /\ (\A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)')
  <2> SUFFICES ASSUME m.type = "1b"
              PROVE  (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
                     /\ (\A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)')
      OBVIOUS
  <2>a. (VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1)
        /\ (\A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b))
        BY <1>0 DEF MsgInvFor
  <2>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
        BY <2>a, VotedForInMonotone
  <2>2. \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
    <3> SUFFICES ASSUME NEW b \in m.maxVBal+1..m.bal-1, NEW v \in Values, VotedForIn(m.acc, v, b)'
                PROVE FALSE OBVIOUS
    <3>1. VotedForIn(m.acc, v, b) BY NoVoteNon2b
    <3> QED BY <3>1, <2>a
  <2> QED BY <2>1, <2>2
<1>2. m.type = "2a" => SafeAt(m.val, m.bal)'
                       /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
  <2> SUFFICES ASSUME m.type = "2a"
              PROVE  SafeAt(m.val, m.bal)'
                     /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
      OBVIOUS
  <2>a. SafeAt(m.val, m.bal)
        /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        BY <1>0 DEF MsgInvFor
  <2>1. SafeAt(m.val, m.bal)' BY <2>a, SafeAtStableNon2b
  <2>2. \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
    <3> SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal PROVE m2 = m OBVIOUS
    <3>1. CASE m2 \in sent BY <3>1, <2>a
    <3>2. CASE m2 = mm
      <4>1. mm.type = "2a" /\ mm.bal = m.bal BY <3>2
      <4>2. ~\E mu \in sent : mu.type = "2a" /\ mu.bal = mm.bal BY <4>1
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>3. m.type = "2b" => \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
  <2> SUFFICES ASSUME m.type = "2b"
              PROVE  \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
      OBVIOUS
  <2>1. PICK m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
        BY <1>0 DEF MsgInvFor
  <2> QED BY <2>1
<1> QED BY <1>1, <1>2, <1>3 DEF MsgInvFor

(***************************************************************************)
(* Preservation of the per-message invariant for old messages, when the    *)
(* added message is a vote ("2b") satisfying the Phase2b guard.            *)
(***************************************************************************)
LEMMA OldPreserved2b ==
  ASSUME NEW mm, TypeOK, MsgInv, sent' = sent \cup {mm}, mm.type = "2b",
         \A m2 \in sent : m2.type \in {"1b", "2b"} /\ m2.acc = mm.acc => mm.bal >= m2.bal,
         NEW m \in sent
  PROVE  MsgInvFor(m)'
<1>0. MsgInvFor(m) BY DEF MsgInv, MsgInvFor
<1>1. m.type = "1b" => (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
                       /\ (\A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)')
  <2> SUFFICES ASSUME m.type = "1b"
              PROVE  (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
                     /\ (\A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)')
      OBVIOUS
  <2>a. (VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1)
        /\ (\A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b))
        BY <1>0 DEF MsgInvFor
  <2>0. m.bal \in Int BY TypeOK DEF TypeOK, Messages, Ballots
  <2>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
        BY <2>a, VotedForInMonotone
  <2>2. \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
    <3> SUFFICES ASSUME NEW b \in m.maxVBal+1..m.bal-1, NEW v \in Values, VotedForIn(m.acc, v, b)'
                PROVE FALSE OBVIOUS
    <3>1. ~(mm.type = "2b" /\ mm.acc = m.acc /\ mm.bal = b)
      <4> SUFFICES ASSUME mm.acc = m.acc, mm.bal = b PROVE FALSE OBVIOUS
      <4>1. m.type \in {"1b", "2b"} /\ m.acc = mm.acc OBVIOUS
      <4>2. mm.bal >= m.bal BY <4>1
      <4>3. b <= m.bal - 1 OBVIOUS
      <4> QED BY <4>2, <4>3, <2>0
    <3>2. VotedForIn(m.acc, v, b) BY <3>1, NoNewVoteGen
    <3> QED BY <3>2, <2>a
  <2> QED BY <2>1, <2>2
<1>2. m.type = "2a" => SafeAt(m.val, m.bal)'
                       /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
  <2> SUFFICES ASSUME m.type = "2a"
              PROVE  SafeAt(m.val, m.bal)'
                     /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
      OBVIOUS
  <2>a. SafeAt(m.val, m.bal)
        /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        BY <1>0 DEF MsgInvFor
  <2>1. SafeAt(m.val, m.bal)' BY <2>a, SafeAtStableVote
  <2>2. \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
    <3> SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal PROVE m2 = m OBVIOUS
    <3>1. m2 # mm OBVIOUS
    <3>2. m2 \in sent BY <3>1
    <3> QED BY <3>2, <2>a
  <2> QED BY <2>1, <2>2
<1>3. m.type = "2b" => \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
  <2> SUFFICES ASSUME m.type = "2b"
              PROVE  \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
      OBVIOUS
  <2>1. PICK m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
        BY <1>0 DEF MsgInvFor
  <2> QED BY <2>1
<1> QED BY <1>1, <1>2, <1>3 DEF MsgInvFor

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv OBVIOUS
<1>1. sent = {} BY DEF Init
<1>2. TypeOK BY <1>1 DEF TypeOK
<1>3. MsgInv BY <1>1 DEF MsgInv
<1> QED BY <1>2, <1>3 DEF Inv

(***************************************************************************)
(* The inductive step.                                                     *)
(***************************************************************************)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
<1> USE DEF Inv
(* --- Stuttering --- *)
<1>S. CASE vars' = vars
  <2>1. sent' = sent BY <1>S DEF vars
  <2> QED BY <2>1 DEF Inv, TypeOK, MsgInv, VotedForIn, SafeAt, WontVoteIn, Messages
(* --- Next --- *)
<1>N. CASE Next
  <2> USE <1>N
  (* ---------- Phase1a ---------- *)
  <2>1. CASE \E b \in Ballots : Phase1a(b)
    <3>1. PICK bb \in Ballots : sent' = sent \cup {[type |-> "1a", bal |-> bb]}
          BY <2>1 DEF Phase1a, Send
    <3> DEFINE mm == [type |-> "1a", bal |-> bb]
    <3>2. sent' = sent \cup {mm} BY <3>1
    <3>3. mm.type # "2b" OBVIOUS
    <3>4. mm \in Messages BY DEF Messages, Ballots
    <3>5. TypeOK' BY <3>2, <3>4 DEF TypeOK
    <3>6. mm.type = "2a" => ~\E mu \in sent : mu.type = "2a" /\ mu.bal = mm.bal OBVIOUS
    <3>7. ASSUME NEW m \in sent PROVE MsgInvFor(m)'
          BY <3>2, <3>3, <3>6, OldPreservedNon2b DEF Inv
    <3>8. MsgInvFor(mm)' BY <3>3 DEF MsgInvFor
    <3>9. \A m \in sent' : MsgInvFor(m)'
      <4> TAKE m \in sent'
      <4>1. m \in sent \/ m = mm BY <3>2
      <4> QED BY <4>1, <3>7, <3>8
    <3>10. MsgInv' BY <3>9 DEF MsgInv, MsgInvFor
    <3> QED BY <3>5, <3>10 DEF Inv
  (* ---------- Phase2a ---------- *)
  <2>2. CASE \E b \in Ballots : Phase2a(b)
    <3>1. PICK b \in Ballots : Phase2a(b) BY <2>2
    <3>2. PICK v \in Values, Q \in Quorums, S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = b} :
            /\ ~\E m \in sent : m.type = "2a" /\ m.bal = b
            /\ \A aa \in Q : \E m \in S : m.acc = aa
            /\ \/ \A m \in S : m.maxVBal = -1
               \/ \E c \in 0..(b-1) : /\ \A m \in S : m.maxVBal =< c
                                      /\ \E m \in S : m.maxVBal = c /\ m.maxVal = v
            /\ sent' = sent \cup {[type |-> "2a", bal |-> b, val |-> v]}
          BY <3>1 DEF Phase2a, Send
    <3> DEFINE mm == [type |-> "2a", bal |-> b, val |-> v]
    <3>3. sent' = sent \cup {mm} BY <3>2
    <3>4. mm.type # "2b" OBVIOUS
    <3>5. mm \in Messages BY <3>2 DEF Messages
    <3>6. TypeOK' BY <3>3, <3>5 DEF TypeOK
    <3>7. mm.type = "2a" => ~\E mu \in sent : mu.type = "2a" /\ mu.bal = mm.bal BY <3>2
    <3>8. ASSUME NEW m \in sent PROVE MsgInvFor(m)'
          BY <3>3, <3>4, <3>7, OldPreservedNon2b DEF Inv
    <3>9. SafeAt(v, b)
      <4> SUFFICES ASSUME NEW b2 \in 0..(b-1)
                  PROVE  \E Q1 \in Quorums : \A aa \in Q1 : VotedForIn(aa, v, b2) \/ WontVoteIn(aa, b2)
          BY DEF SafeAt
      <4>cases. \/ \A m \in S : m.maxVBal = -1
                \/ \E c \in 0..(b-1) : /\ \A m \in S : m.maxVBal =< c
                                       /\ \E m \in S : m.maxVBal = c /\ m.maxVal = v
                BY <3>2
      <4>bb. b \in Nat /\ b2 \in Nat /\ b2 <= b - 1 BY DEF Ballots
      <4>A. CASE \A m \in S : m.maxVBal = -1
        <5>1. \A aa \in Q : VotedForIn(aa, v, b2) \/ WontVoteIn(aa, b2)
          <6> TAKE aa \in Q
          <6>1. PICK ma \in S : ma.acc = aa BY <3>2
          <6>2. ma \in sent /\ ma.type = "1b" /\ ma.bal = b BY <6>1, <3>2
          <6>3. ma.maxVBal = -1 BY <4>A, <6>1
          <6>4. MsgInvFor(ma) BY <6>2 DEF MsgInv, MsgInvFor
          <6>5. \A bk \in ma.maxVBal+1..ma.bal-1 : ~\E vv \in Values : VotedForIn(ma.acc, vv, bk)
                BY <6>4, <6>2 DEF MsgInvFor
          <6>6. b2 \in ma.maxVBal+1..ma.bal-1 BY <6>2, <6>3, <4>bb
          <6>7. ~\E vv \in Values : VotedForIn(aa, vv, b2) BY <6>5, <6>6, <6>1
          <6>8. \E msg \in sent : msg.type \in {"1b", "2b"} /\ msg.acc = aa /\ msg.bal > b2
                BY <6>2, <6>1, <4>bb
          <6>9. WontVoteIn(aa, b2) BY <6>7, <6>8 DEF WontVoteIn
          <6> QED BY <6>9
        <5> QED BY <5>1
      <4>B. CASE \E c \in 0..(b-1) : /\ \A m \in S : m.maxVBal =< c
                                     /\ \E m \in S : m.maxVBal = c /\ m.maxVal = v
        <5>1. PICK c \in 0..(b-1) : (\A m \in S : m.maxVBal =< c)
                                    /\ (\E m \in S : m.maxVBal = c /\ m.maxVal = v) BY <4>B
        <5>2. PICK mc \in S : mc.maxVBal = c /\ mc.maxVal = v BY <5>1
        <5>3. mc \in sent /\ mc.type = "1b" /\ mc.bal = b BY <5>2, <3>2
        <5>cc. c \in Nat /\ c <= b - 1 BY <5>1
        <5>B1. CASE b2 > c
          <6>1. \A aa \in Q : VotedForIn(aa, v, b2) \/ WontVoteIn(aa, b2)
            <7> TAKE aa \in Q
            <7>1. PICK ma \in S : ma.acc = aa BY <3>2
            <7>2. ma \in sent /\ ma.type = "1b" /\ ma.bal = b BY <7>1, <3>2
            <7>3. ma.maxVBal =< c BY <5>1, <7>1
            <7>4. ma.maxVBal \in Int BY <7>2, TypeOK DEF TypeOK, Messages, Ballots
            <7>5. MsgInvFor(ma) BY <7>2 DEF MsgInv, MsgInvFor
            <7>6. \A bk \in ma.maxVBal+1..ma.bal-1 : ~\E vv \in Values : VotedForIn(ma.acc, vv, bk)
                  BY <7>5, <7>2 DEF MsgInvFor
            <7>7. b2 \in ma.maxVBal+1..ma.bal-1 BY <7>2, <7>3, <7>4, <5>cc, <5>B1, <4>bb
            <7>8. ~\E vv \in Values : VotedForIn(aa, vv, b2) BY <7>6, <7>7, <7>1
            <7>9. \E msg \in sent : msg.type \in {"1b", "2b"} /\ msg.acc = aa /\ msg.bal > b2
                  BY <7>2, <7>1, <4>bb
            <7>10. WontVoteIn(aa, b2) BY <7>8, <7>9 DEF WontVoteIn
            <7> QED BY <7>10
          <6> QED BY <6>1
        <5>B2. CASE b2 = c
          <6>1. \A aa \in Q : VotedForIn(aa, v, b2) \/ WontVoteIn(aa, b2)
            <7> TAKE aa \in Q
            <7>1. PICK ma \in S : ma.acc = aa BY <3>2
            <7>2. ma \in sent /\ ma.type = "1b" /\ ma.bal = b BY <7>1, <3>2
            <7>3. ma.maxVBal =< c BY <5>1, <7>1
            <7>4. ma.maxVBal \in Int BY <7>2, TypeOK DEF TypeOK, Messages, Ballots
            <7>5. MsgInvFor(ma) BY <7>2 DEF MsgInv, MsgInvFor
            <7>B2a. CASE ma.maxVBal < c
              <8>1. \A bk \in ma.maxVBal+1..ma.bal-1 : ~\E vv \in Values : VotedForIn(ma.acc, vv, bk)
                    BY <7>5, <7>2 DEF MsgInvFor
              <8>2. b2 \in ma.maxVBal+1..ma.bal-1 BY <7>2, <7>4, <7>B2a, <5>cc, <5>B2, <4>bb
              <8>3. ~\E vv \in Values : VotedForIn(aa, vv, b2) BY <8>1, <8>2, <7>1
              <8>4. \E msg \in sent : msg.type \in {"1b", "2b"} /\ msg.acc = aa /\ msg.bal > b2
                    BY <7>2, <7>1, <4>bb
              <8>5. WontVoteIn(aa, b2) BY <8>3, <8>4 DEF WontVoteIn
              <8> QED BY <8>5
            <7>B2b. CASE ma.maxVBal = c
              <8>1. ma.maxVBal # -1 BY <7>B2b, <5>cc
              <8>2. VotedForIn(ma.acc, ma.maxVal, ma.maxVBal) \/ ma.maxVBal = -1
                    BY <7>5, <7>2 DEF MsgInvFor
              <8>3. VotedForIn(aa, ma.maxVal, c) BY <8>1, <8>2, <7>B2b, <7>1
              <8>4. mc.maxVBal # -1 BY <5>2, <5>cc
              <8>5. VotedForIn(mc.acc, mc.maxVal, mc.maxVBal) \/ mc.maxVBal = -1
                <9>1. MsgInvFor(mc) BY <5>3 DEF MsgInv, MsgInvFor
                <9> QED BY <9>1, <5>3 DEF MsgInvFor
              <8>6. VotedForIn(mc.acc, v, c) BY <8>4, <8>5, <5>2
              <8>7. ma.maxVal = v BY <8>3, <8>6, VotedOnce, MsgInv
              <8>8. VotedForIn(aa, v, b2) BY <8>3, <8>7, <5>B2
              <8> QED BY <8>8
            <7> QED BY <7>3, <7>4, <5>cc, <7>B2a, <7>B2b
          <6> QED BY <6>1
        <5>B3. CASE b2 < c
          <6>1. mc.maxVBal # -1 BY <5>2, <5>cc
          <6>2. VotedForIn(mc.acc, mc.maxVal, mc.maxVBal) \/ mc.maxVBal = -1
            <7>1. MsgInvFor(mc) BY <5>3 DEF MsgInv, MsgInvFor
            <7> QED BY <7>1, <5>3 DEF MsgInvFor
          <6>3. VotedForIn(mc.acc, v, c) BY <6>1, <6>2, <5>2
          <6>4. PICK m2b \in sent : m2b.type = "2b" /\ m2b.val = v /\ m2b.bal = c /\ m2b.acc = mc.acc
                BY <6>3 DEF VotedForIn
          <6>5. PICK m2a \in sent : m2a.type = "2a" /\ m2a.bal = c /\ m2a.val = v
                BY <6>4, MsgInv DEF MsgInv
          <6>6. SafeAt(m2a.val, m2a.bal) BY <6>5, MsgInv DEF MsgInv
          <6>7. SafeAt(v, c) BY <6>6, <6>5
          <6>8. b2 \in 0..(c-1) BY <5>B3, <5>cc, <4>bb
          <6>9. \E Q1 \in Quorums : \A aa \in Q1 : VotedForIn(aa, v, b2) \/ WontVoteIn(aa, b2)
                BY <6>7, <6>8 DEF SafeAt
          <6> QED BY <6>9
        <5> QED BY <5>cc, <4>bb, <5>B1, <5>B2, <5>B3
      <4> QED BY <4>cases, <4>A, <4>B
    <3>10. SafeAt(v, b)' BY <3>3, <3>4, <3>9, SafeAtStableNon2b
    <3>11. MsgInvFor(mm)'
      <4>1. mm.type = "2a" => SafeAt(mm.val, mm.bal)'
                              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = mm.bal) => m2 = mm
        <5>1. SafeAt(mm.val, mm.bal)' BY <3>10
        <5>2. \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = mm.bal) => m2 = mm
          <6> SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = mm.bal PROVE m2 = mm OBVIOUS
          <6>1. CASE m2 \in sent BY <6>1, <3>2
          <6>2. CASE m2 = mm BY <6>2
          <6> QED BY <6>1, <6>2, <3>3
        <5> QED BY <5>1, <5>2
      <4>2. mm.type = "1b" => (VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)' \/ mm.maxVBal = -1)
                              /\ (\A bk \in mm.maxVBal+1..mm.bal-1 : ~\E vv \in Values : VotedForIn(mm.acc, vv, bk)')
            OBVIOUS
      <4>3. mm.type = "2b" => \E m2 \in sent' : m2.type = "2a" /\ m2.bal = mm.bal /\ m2.val = mm.val
            OBVIOUS
      <4> QED BY <4>1, <4>2, <4>3 DEF MsgInvFor
    <3>12. \A m \in sent' : MsgInvFor(m)'
      <4> TAKE m \in sent'
      <4>1. m \in sent \/ m = mm BY <3>3
      <4> QED BY <4>1, <3>8, <3>11
    <3>13. MsgInv' BY <3>12 DEF MsgInv, MsgInvFor
    <3> QED BY <3>6, <3>13 DEF Inv
  (* ---------- Phase1b ---------- *)
  <2>3. CASE \E a \in Acceptors : Phase1b(a)
    <3>1. PICK a \in Acceptors : Phase1b(a) BY <2>3
    <3>2. PICK m0 \in sent, r \in last_voted(a) :
            /\ m0.type = "1a"
            /\ \A m2 \in sent : m2.type \in {"1b", "2b"} /\ m2.acc = a => m0.bal > m2.bal
            /\ sent' = sent \cup {[type |-> "1b", bal |-> m0.bal, maxVBal |-> r.bal,
                                   maxVal |-> r.val, acc |-> a]}
          BY <3>1 DEF Phase1b, Send
    <3> DEFINE mm == [type |-> "1b", bal |-> m0.bal, maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a]
    <3>3. sent' = sent \cup {mm} BY <3>2
    <3>4. mm.type # "2b" OBVIOUS
    <3>5. m0.bal \in Ballots BY <3>2, TypeOK DEF TypeOK, Messages
    <3>6. mm.type = "2a" => ~\E mu \in sent : mu.type = "2a" /\ mu.bal = mm.bal OBVIOUS
    <3>7. ASSUME NEW m \in sent PROVE MsgInvFor(m)'
          BY <3>3, <3>4, <3>6, OldPreservedNon2b DEF Inv
    (* analyze last_voted(a) *)
    <3>8. CASE {mq \in sent : mq.type = "2b" /\ mq.acc = a} # {}
      <4>1. r \in {mq \in {md \in sent : md.type = "2b" /\ md.acc = a} :
                     \A m2 \in {md \in sent : md.type = "2b" /\ md.acc = a} : mq.bal >= m2.bal}
            BY <3>2, <3>8 DEF last_voted
      <4>2. r \in sent /\ r.type = "2b" /\ r.acc = a BY <4>1
      <4>3. \A m2 \in {md \in sent : md.type = "2b" /\ md.acc = a} : r.bal >= m2.bal BY <4>1
      <4>4. r.bal \in Ballots /\ r.val \in Values BY <4>2, TypeOK DEF TypeOK, Messages
      <4>5. mm \in Messages BY <3>5, <4>4, <3>1 DEF Messages
      <4>6. TypeOK' BY <3>3, <4>5 DEF TypeOK
      <4>7. VotedForIn(a, r.val, r.bal) BY <4>2 DEF VotedForIn
      <4>8. VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)' \/ mm.maxVBal = -1
            BY <4>7, <3>3, VotedForInMonotone
      <4>9. \A bk \in mm.maxVBal+1..mm.bal-1 : ~\E vv \in Values : VotedForIn(mm.acc, vv, bk)'
        <5> SUFFICES ASSUME NEW bk \in mm.maxVBal+1..mm.bal-1, NEW vv \in Values, VotedForIn(a, vv, bk)'
                    PROVE FALSE BY DEF VotedForIn
        <5>1. VotedForIn(a, vv, bk) BY <3>3, <3>4, NoVoteNon2b
        <5>2. PICK mb \in sent : mb.type = "2b" /\ mb.val = vv /\ mb.bal = bk /\ mb.acc = a
              BY <5>1 DEF VotedForIn
        <5>3. mb \in {mq \in sent : mq.type = "2b" /\ mq.acc = a} BY <5>2
        <5>4. r.bal >= bk BY <4>3, <5>3, <5>2
        <5>5. bk >= r.bal + 1 BY <4>4 DEF Ballots
        <5> QED BY <5>4, <5>5, <4>4 DEF Ballots
      <4>10. MsgInvFor(mm)' BY <4>8, <4>9 DEF MsgInvFor
      <4>11. \A m \in sent' : MsgInvFor(m)'
        <5> TAKE m \in sent'
        <5>1. m \in sent \/ m = mm BY <3>3
        <5> QED BY <5>1, <3>7, <4>10
      <4>12. MsgInv' BY <4>11 DEF MsgInv, MsgInvFor
      <4> QED BY <4>6, <4>12 DEF Inv
    <3>9. CASE {mq \in sent : mq.type = "2b" /\ mq.acc = a} = {}
      <4>1. r = [bal |-> -1, val |-> None] BY <3>2, <3>9 DEF last_voted
      <4>2. r.bal = -1 /\ r.val = None BY <4>1
      <4>3. mm \in Messages BY <3>5, <4>2, <3>1 DEF Messages
      <4>4. TypeOK' BY <3>3, <4>3 DEF TypeOK
      <4>5. VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)' \/ mm.maxVBal = -1 BY <4>2
      <4>6. \A bk \in mm.maxVBal+1..mm.bal-1 : ~\E vv \in Values : VotedForIn(mm.acc, vv, bk)'
        <5> SUFFICES ASSUME NEW bk \in mm.maxVBal+1..mm.bal-1, NEW vv \in Values, VotedForIn(a, vv, bk)'
                    PROVE FALSE BY DEF VotedForIn
        <5>1. VotedForIn(a, vv, bk) BY <3>3, <3>4, NoVoteNon2b
        <5>2. PICK mb \in sent : mb.type = "2b" /\ mb.val = vv /\ mb.bal = bk /\ mb.acc = a
              BY <5>1 DEF VotedForIn
        <5>3. mb \in {mq \in sent : mq.type = "2b" /\ mq.acc = a} BY <5>2
        <5> QED BY <5>3, <3>9
      <4>7. MsgInvFor(mm)' BY <4>5, <4>6 DEF MsgInvFor
      <4>8. \A m \in sent' : MsgInvFor(m)'
        <5> TAKE m \in sent'
        <5>1. m \in sent \/ m = mm BY <3>3
        <5> QED BY <5>1, <3>7, <4>7
      <4>9. MsgInv' BY <4>8 DEF MsgInv, MsgInvFor
      <4> QED BY <4>4, <4>9 DEF Inv
    <3> QED BY <3>8, <3>9
  (* ---------- Phase2b ---------- *)
  <2>4. CASE \E a \in Acceptors : Phase2b(a)
    <3>1. PICK a \in Acceptors : Phase2b(a) BY <2>4
    <3>2. PICK m0 \in sent :
            /\ m0.type = "2a"
            /\ \A m2 \in sent : m2.type \in {"1b", "2b"} /\ m2.acc = a => m0.bal >= m2.bal
            /\ sent' = sent \cup {[type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a]}
          BY <3>1 DEF Phase2b, Send
    <3> DEFINE mm == [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a]
    <3>3. sent' = sent \cup {mm} BY <3>2
    <3>4. mm.type = "2b" OBVIOUS
    <3>5. m0.bal \in Ballots /\ m0.val \in Values BY <3>2, TypeOK DEF TypeOK, Messages
    <3>6. mm \in Messages BY <3>5, <3>1 DEF Messages
    <3>7. TypeOK' BY <3>3, <3>6 DEF TypeOK
    <3>8. \A m2 \in sent : m2.type \in {"1b", "2b"} /\ m2.acc = mm.acc => mm.bal >= m2.bal
          BY <3>2
    <3>9. ASSUME NEW m \in sent PROVE MsgInvFor(m)'
          BY <3>3, <3>4, <3>8, OldPreserved2b DEF Inv
    <3>10. MsgInvFor(mm)'
      <4>1. mm.type = "2b" => \E m2 \in sent' : m2.type = "2a" /\ m2.bal = mm.bal /\ m2.val = mm.val
        <5>1. m0 \in sent' /\ m0.type = "2a" /\ m0.bal = mm.bal /\ m0.val = mm.val BY <3>2, <3>3
        <5> QED BY <5>1
      <4>2. mm.type = "1b" => (VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)' \/ mm.maxVBal = -1)
                              /\ (\A bk \in mm.maxVBal+1..mm.bal-1 : ~\E vv \in Values : VotedForIn(mm.acc, vv, bk)')
            OBVIOUS
      <4>3. mm.type = "2a" => SafeAt(mm.val, mm.bal)'
                             /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = mm.bal) => m2 = mm
            OBVIOUS
      <4> QED BY <4>1, <4>2, <4>3 DEF MsgInvFor
    <3>11. \A m \in sent' : MsgInvFor(m)'
      <4> TAKE m \in sent'
      <4>1. m \in sent \/ m = mm BY <3>3
      <4> QED BY <4>1, <3>9, <3>10
    <3>12. MsgInv' BY <3>11 DEF MsgInv, MsgInvFor
    <3> QED BY <3>7, <3>12 DEF Inv
  <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1> QED BY <1>S, <1>N

THEOREM Invariant == Spec => []Inv
<1>1. Init => Inv BY InitInv
<1>2. Inv /\ [Next]_vars => Inv' BY NextInv
<1> QED BY <1>1, <1>2, PTL DEF Spec


=============================================================================
\* Modification History
\* Last modified Mon Jul 22 20:43:22 CST 2019 by hengxin
\* Last modified Sat Dec 09 09:56:40 EST 2017 by Saksham
\* Last modified Tue Nov 21 19:12:25 EST 2017 by saksh
\* Last modified Fri Nov 28 10:39:17 PST 2014 by lamport
\* Last modified Sun Nov 23 14:45:09 PST 2014 by lamport
\* Last modified Mon Nov 24 02:03:02 CET 2014 by merz
\* Last modified Sat Nov 22 12:04:19 CET 2014 by merz
\* Last modified Fri Nov 21 17:40:41 PST 2014 by lamport
\* Last modified Tue Mar 18 11:37:57 CET 2014 by doligez
\* Last modified Sat Nov 24 18:53:09 GMT-03:00 2012 by merz
\* Created Sat Nov 17 16:02:06 PST 2012 by lamport