------------------------------- MODULE PaxosHistVar_SafeAtStable --------------------------
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
PROOF
<1>1. SUFFICES ASSUME Inv /\ Next
                PROVE  \A v \in Values, b \in Ballots:
                         SafeAt(v, b) => SafeAt(v, b)'
  OBVIOUS
<1>2. TAKE v \in Values, b \in Ballots
<1>3. SUFFICES ASSUME SafeAt(v, b)
                PROVE  SafeAt(v, b)'
  OBVIOUS
<1>4. (0..(b-1))' = 0..(b-1)
  OBVIOUS
<1>5. SUFFICES ASSUME NEW b2 \in 0..(b-1)
                PROVE  \E Q \in Quorums :
                         \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
  BY <1>4 DEF SafeAt
<1>6. PICK Q \in Quorums :
          \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
  BY <1>3, <1>5 DEF SafeAt
<1>7. \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
  PROOF
  <2>1. TAKE a \in Q
  <2>2. VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
    BY <1>6, <2>1
  <2>3. CASE VotedForIn(a, v, b2)
    PROOF
    <3>1. PICK vote \in sent :
              /\ vote.type = "2b"
              /\ vote.val = v
              /\ vote.bal = b2
              /\ vote.acc = a
      BY <2>3 DEF VotedForIn
    <3>2. CASE \E b0 \in Ballots : Phase1a(b0) \/ Phase2a(b0)
      BY <3>1, <3>2 DEF VotedForIn, Phase1a, Phase2a, Send
    <3>3. CASE \E a0 \in Acceptors : Phase1b(a0) \/ Phase2b(a0)
      BY <3>1, <3>3 DEF VotedForIn, Phase1b, Phase2b, Send
    <3> QED
      BY <1>1, <3>2, <3>3 DEF Next
  <2>4. CASE WontVoteIn(a, b2)
    PROOF
    <3>1. PICK old \in sent :
              old.type \in {"1b", "2b"} /\ old.acc = a /\ old.bal > b2
      BY <2>4 DEF WontVoteIn
    <3>2. \A u \in Values : ~ VotedForIn(a, u, b2)
      BY <2>4 DEF WontVoteIn
    <3>3. CASE \E b0 \in Ballots : Phase1a(b0) \/ Phase2a(b0)
      BY <3>1, <3>2, <3>3 DEF WontVoteIn, VotedForIn, Phase1a, Phase2a, Send
    <3>4. CASE \E a0 \in Acceptors : Phase1b(a0)
      BY <3>1, <3>2, <3>4 DEF WontVoteIn, VotedForIn, Phase1b, Send
    <3>5. CASE \E a0 \in Acceptors : Phase2b(a0)
      PROOF
      <4>1. PICK a0 \in Acceptors : Phase2b(a0)
        BY <3>5
      <4>2. PICK m \in sent :
              /\ m.type = "2a"
              /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a0 => m.bal >= m2.bal
              /\ sent' = sent \cup {[type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a0]}
        BY <4>1 DEF Phase2b, Send
      <4>3. TypeOK
        BY <1>1 DEF Inv
      <4>4. old.bal \in Ballots
        BY <3>1, <4>3 DEF TypeOK, Messages
      <4>5. m.bal \in Ballots
        BY <4>2, <4>3 DEF TypeOK, Messages
      <4>6. b2 \in Ballots
        BY <1>5 DEF Ballots
      <4>7. a0 = a => m.bal >= old.bal
        BY <3>1, <4>2
      <4>8. a0 = a => m.bal > b2
        BY <3>1, <4>4, <4>5, <4>6, <4>7 DEF Ballots
      <4>9. \A u \in Values : ~ VotedForIn(a, u, b2)'
        BY <3>2, <4>2, <4>8 DEF VotedForIn
      <4>10. old \in sent'
        BY <3>1, <4>2
      <4> QED
        BY <3>1, <4>9, <4>10 DEF WontVoteIn
    <3> QED
      BY <1>1, <3>3, <3>4, <3>5 DEF Next
  <2> QED
    BY <2>2, <2>3, <2>4
<1> QED
  BY <1>6, <1>7

=============================================================================
