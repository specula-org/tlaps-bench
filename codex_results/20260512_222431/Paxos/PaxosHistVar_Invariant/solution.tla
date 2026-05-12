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
LEMMA VotedInv == 
        MsgInv /\ TypeOK => 
            \A a \in Acceptors, v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => SafeAt(v, b)
  PROOF OMITTED

LEMMA VotedOnce == 
        MsgInv =>  \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
                       VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b) is stable, meaning that once it becomes true, it *)
(* remains true throughout the rest of the excecution.                     *)
(***************************************************************************)
LEMMA SafeAtStable == Inv /\ Next => 
                          \A v \in Values, b \in Ballots:
                                  SafeAt(v, b) => SafeAt(v, b)'
  PROOF OMITTED

THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots
<1>1. Init => Inv
  BY Isa DEF Init, Inv, TypeOK, MsgInv, VotedForIn, Messages
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE Next
  <2>2. TypeOK'
    BY SMTT(60) DEF vars, Inv, TypeOK, Messages, Next, Phase1a, Phase2a, Phase1b, Phase2b, Send, last_voted
  <2>3. MsgInv'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE MsgInv'
      <4>1. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
        BY <3>1 DEF Phase1a, Send, VotedForIn
      <4>. QED
        BY <2>2, <3>1, <4>1, SafeAtStable DEF Inv, MsgInv, TypeOK, Messages, Phase1a, Send
    <3>2. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE MsgInv'
      <4>0. PICK m \in sent, r \in last_voted(a) :
             /\ m.type = "1a"
             /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal > m2.bal
             /\ Send([type |-> "1b", bal |-> m.bal,
                      maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a])
        BY <3>2 DEF Phase1b
      <4>1. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
        BY <4>0 DEF Send, VotedForIn
      <4>. DEFINE mm == [type |-> "1b", bal |-> m.bal,
                         maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a]
      <4>2. VotedForIn(mm.acc, mm.maxVal, mm.maxVBal) \/ mm.maxVBal = -1
        BY <4>0, Isa DEF last_voted, VotedForIn
      <4>3. \A c \in (mm.maxVBal+1)..(mm.bal-1) :
               ~\E v \in Values : VotedForIn(mm.acc, v, c)
        <5> SUFFICES ASSUME NEW c \in (mm.maxVBal+1)..(mm.bal-1),
                            NEW v \in Values,
                            VotedForIn(mm.acc, v, c)
                     PROVE  FALSE
          BY Zenon
        <5>1. CASE {m2 \in sent : m2.type = "2b" /\ m2.acc = a} = {}
          BY <4>0, <5>1 DEF last_voted, VotedForIn
        <5>2. CASE {m2 \in sent : m2.type = "2b" /\ m2.acc = a} # {}
          <6>1. r \in {m2 \in sent : m2.type = "2b" /\ m2.acc = a}
                  /\ \A m2 \in {m2 \in sent : m2.type = "2b" /\ m2.acc = a} : r.bal >= m2.bal
            BY <4>0, <5>2 DEF last_voted
          <6>2. PICK m2 \in sent :
                   /\ m2.type = "2b"
                   /\ m2.val = v
                   /\ m2.bal = c
                   /\ m2.acc = a
            BY DEF VotedForIn
          <6>3. m2 \in {m2 \in sent : m2.type = "2b" /\ m2.acc = a}
            BY <6>2
          <6>4. c =< r.bal
            BY <6>1, <6>2, <6>3, SimpleArithmetic
          <6>5. r.bal \in Ballots \cup {-1} /\ m.bal \in Ballots
            BY <4>0, <6>1 DEF last_voted, TypeOK, Messages
          <6>6. c > r.bal
            BY <6>5, SMT DEF mm
          <6>. QED BY <6>4, <6>5, <6>6, SimpleArithmetic
        <5>. QED BY <5>1, <5>2
      <4>. QED
        BY <2>2, <3>2, <4>0, <4>1, <4>2, <4>3, SafeAtStable
           DEF Inv, MsgInv, TypeOK, Messages, Send
    <3>3. ASSUME NEW b \in Ballots, Phase2a(b) PROVE MsgInv'
      <4>1. ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b)
        BY <3>3 DEF Phase2a
      <4>2. PICK v \in Values, Q \in Quorums,
                   S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = b} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) :
                       /\ \A m \in S : m.maxVBal =< c
                       /\ \E m \in S : /\ m.maxVBal = c
                                       /\ m.maxVal = v
               /\ Send([type |-> "2a", bal |-> b, val |-> v])
        BY <3>3 DEF Phase2a
      <4>. DEFINE mm == [type |-> "2a", bal |-> b, val |-> v]
      <4>3. sent' = sent \cup {mm}
        BY <4>2 DEF Send
      <4>4. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
        BY <4>3 DEF VotedForIn
      <4>5. \A ma \in sent' : ma.type = "2a" /\ ma.bal = mm.bal => ma = mm
        BY <4>1, <4>3 DEF Inv, MsgInv
      <4>6. SafeAt(v, b)
        <5>0. /\ \A a \in Q : \E m \in S : m.acc = a
              /\ \/ \A m \in S : m.maxVBal = -1
                 \/ \E c \in 0..(b-1) :
                      /\ \A m \in S : m.maxVBal =< c
                      /\ \E m \in S : /\ m.maxVBal = c
                                      /\ m.maxVal = v
          BY <4>2
        <5>1. CASE \A m \in S : m.maxVBal = -1
          <6> SUFFICES ASSUME NEW d \in 0..(b-1)
                       PROVE  \E QQ \in Quorums : \A q \in QQ :
                                 VotedForIn(q, v, d) \/ WontVoteIn(q, d)
            BY DEF SafeAt
          <6>1. \A q \in Q : WontVoteIn(q, d)
            <7> SUFFICES ASSUME NEW q \in Q PROVE WontVoteIn(q, d)
              BY Zenon
            <7>1. PICK mq \in S : mq.acc = q
              BY <5>0
            <7>2. mq \in sent /\ mq.type = "1b" /\ mq.bal = b /\ mq.maxVBal = -1 /\ mq.acc = q
              BY <4>2, <5>1, <7>1
            <7>3. d \in (mq.maxVBal+1)..(mq.bal-1)
              BY <7>2, SMT
            <7>4. ~ \E vv \in Values : VotedForIn(q, vv, d)
              BY <7>2, <7>3 DEF Inv, MsgInv
            <7>5. \E m0 \in sent : m0.type \in {"1b", "2b"} /\ m0.acc = q /\ m0.bal > d
              BY <7>2, SMT
            <7>. QED BY <7>4, <7>5 DEF WontVoteIn
          <6>. QED BY <5>0, <6>1
        <5>2. ASSUME NEW c \in 0..(b-1),
                     \A m \in S : m.maxVBal =< c,
                     NEW ma \in S, ma.maxVBal = c, ma.maxVal = v
              PROVE  SafeAt(v, b)
          <6> SUFFICES ASSUME NEW d \in 0..(b-1)
                       PROVE  \E QQ \in Quorums : \A q \in QQ :
                                 VotedForIn(q, v, d) \/ WontVoteIn(q, d)
            BY DEF SafeAt
          <6>1. CASE d \in 0..(c-1)
            BY <5>0, <5>2, <6>1, VotedInv, SMT DEF Inv, SafeAt, MsgInv, TypeOK, Messages
          <6>2. CASE d = c
            <7>1. VotedForIn(ma.acc, v, c)
              BY <5>0, <5>2, SMT DEF Inv, MsgInv
            <7>2. \A q \in Q, w \in Values : VotedForIn(q, w, c) => w = v
              BY <7>1, <5>0, <5>2, VotedOnce, QuorumAssumption, SMT DEF Inv, TypeOK, Messages
            <7>3. \A q \in Q : WontVoteIn(q, c) \/ VotedForIn(q, v, c)
              BY <5>0, <5>2, <6>2, <7>2, SMT DEF Inv, MsgInv, WontVoteIn, TypeOK, Messages
            <7>. QED BY <5>0, <6>2, <7>3
          <6>3. CASE d \in (c+1)..(b-1)
            BY <5>0, <5>2, <6>3, SMT DEF Inv, MsgInv, TypeOK, Messages, WontVoteIn
          <6>. QED BY <6>1, <6>2, <6>3
        <5>. QED BY <4>2, <5>1, <5>2
      <4>7. SafeAt(mm.val, mm.bal)'
        BY <2>2, <3>3, <4>6, SafeAtStable DEF Inv, Next
      <4>. QED
        BY <2>2, <3>3, <4>3, <4>4, <4>5, <4>7, SafeAtStable
           DEF Inv, MsgInv, TypeOK, Messages
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE MsgInv'
      <4>0. PICK m \in sent :
             /\ m.type = "2a"
             /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
        BY <3>4 DEF Phase2b
      <4>1. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=>
                              VotedForIn(aa, vv, bb) \/ (aa = a /\ vv = m.val /\ bb = m.bal)
        BY <4>0 DEF VotedForIn, Send
      <4>2. \A mm \in sent : mm.type = "1b"
               => \A v \in Values, c \in (mm.maxVBal+1)..(mm.bal-1) :
                    ~ VotedForIn(mm.acc, v, c) => ~ VotedForIn(mm.acc, v, c)'
        BY <3>4, <4>0, <4>1, SMT DEF Phase2b, Inv, MsgInv, TypeOK, Messages
      <4>. QED
        BY <2>2, <3>4, <4>0, <4>1, <4>2, SafeAtStable, SMT DEF Inv, MsgInv, TypeOK, Messages, Send
    <3>. QED BY <2>1, <3>1, <3>2, <3>3, <3>4, SMT DEF Next
  <2>4. Inv'
    BY <2>2, <2>3 DEF Inv
  <2>5. CASE UNCHANGED vars
    BY <2>5, SMT DEF vars, Inv, TypeOK, MsgInv, VotedForIn, SafeAt, WontVoteIn
  <2>. QED BY <2>1, <2>4, <2>5, SMT DEF vars
<1>. QED BY <1>1, <1>2, PTL DEF Spec

=============================================================================
