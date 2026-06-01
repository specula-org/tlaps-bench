------------------------------- MODULE PaxosHistVar_Consistent --------------------------
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
  PROOF OMITTED

THEOREM Consistent == Spec => []Consistency
PROOF
  <1>1. ASSUME Inv
         PROVE Consistency
    <2>1. MsgInv /\ TypeOK
      BY <1>1 DEF Inv
    <2>2. SUFFICES ASSUME NEW v1 \in Values, NEW v2 \in Values
                     PROVE Chosen(v1) /\ Chosen(v2) => v1 = v2
      BY Zenon DEF Consistency
    <2>3. ASSUME Chosen(v1), Chosen(v2)
           PROVE v1 = v2
      <3>1. PICK b1 \in Ballots : ChosenIn(v1, b1)
        BY <2>3 DEF Chosen
      <3>2. PICK b2 \in Ballots : ChosenIn(v2, b2)
        BY <2>3 DEF Chosen
      <3>3. CASE b1 = b2
        <4>1. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
          BY <3>1 DEF ChosenIn
        <4>2. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
          BY <3>2 DEF ChosenIn
        <4>3. PICK a \in Q1 \cap Q2 : TRUE
          BY <4>1, <4>2, QuorumAssumption
        <4>4. VotedForIn(a, v1, b1) /\ VotedForIn(a, v2, b1)
          BY <3>3, <4>1, <4>2, <4>3
        <4> QED BY <2>1, <4>1, <4>2, <4>3, <4>4, VotedOnce, QuorumAssumption
      <3>4. CASE b1 < b2
        <4>1. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
          BY <3>2 DEF ChosenIn
        <4>2. Q2 # {}
          BY <4>1, QuorumAssumption
        <4>3. PICK a2 \in Q2 : TRUE
          BY <4>2
        <4>4. VotedForIn(a2, v2, b2)
          BY <4>1, <4>3
        <4>5. SafeAt(v2, b2)
          BY <2>1, <4>1, <4>3, <4>4, VotedInv, QuorumAssumption
        <4>6. b1 \in 0..(b2-1)
          BY <3>1, <3>2, <3>4 DEF Ballots
        <4>7. PICK Q \in Quorums :
                  \A a \in Q : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
          BY <4>5, <4>6 DEF SafeAt
        <4>8. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
          BY <3>1 DEF ChosenIn
        <4>9. PICK a \in Q \cap Q1 : TRUE
          BY <4>7, <4>8, QuorumAssumption
        <4>10. VotedForIn(a, v1, b1)
          BY <4>8, <4>9
        <4>11. VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
          BY <4>7, <4>9
        <4> QED BY <2>1, <4>7, <4>8, <4>9, <4>10, <4>11, VotedOnce, QuorumAssumption DEF WontVoteIn
      <3>5. CASE b2 < b1
        <4>1. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
          BY <3>1 DEF ChosenIn
        <4>2. Q1 # {}
          BY <4>1, QuorumAssumption
        <4>3. PICK a1 \in Q1 : TRUE
          BY <4>2
        <4>4. VotedForIn(a1, v1, b1)
          BY <4>1, <4>3
        <4>5. SafeAt(v1, b1)
          BY <2>1, <4>1, <4>3, <4>4, VotedInv, QuorumAssumption
        <4>6. b2 \in 0..(b1-1)
          BY <3>1, <3>2, <3>5 DEF Ballots
        <4>7. PICK Q \in Quorums :
                  \A a \in Q : VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
          BY <4>5, <4>6 DEF SafeAt
        <4>8. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
          BY <3>2 DEF ChosenIn
        <4>9. PICK a \in Q \cap Q2 : TRUE
          BY <4>7, <4>8, QuorumAssumption
        <4>10. VotedForIn(a, v2, b2)
          BY <4>8, <4>9
        <4>11. VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
          BY <4>7, <4>9
        <4> QED BY <2>1, <4>7, <4>8, <4>9, <4>10, <4>11, VotedOnce, QuorumAssumption DEF WontVoteIn
      <3> QED BY <3>3, <3>4, <3>5, <3>1, <3>2 DEF Ballots
    <2> QED BY <2>2, <2>3
  <1>2. Spec => []Inv BY Invariant
  <1>3. []Inv => []Consistency BY <1>1, PTL
  <1> QED BY <1>2, <1>3

=============================================================================
