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

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b) is stable, meaning that once it becomes true, it *)
(* remains true throughout the rest of the excecution.                     *)
(***************************************************************************)


(***************************************************************************)
(* Basic facts about Quorums.                                              *)
(***************************************************************************)
LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
BY QuorumAssumption

LEMMA QuorumIntersect ==
  \A Q1, Q2 \in Quorums : \E a \in Acceptors : a \in Q1 /\ a \in Q2
PROOF
  <1> SUFFICES ASSUME NEW Q1 \in Quorums, NEW Q2 \in Quorums
               PROVE  \E a \in Acceptors : a \in Q1 /\ a \in Q2
    OBVIOUS
  <1>1. Q1 \cap Q2 # {} BY QuorumAssumption
  <1>2. Q1 \subseteq Acceptors BY QuorumAssumption
  <1>3. PICK a \in Q1 \cap Q2 : TRUE BY <1>1
  <1> QED BY <1>2, <1>3

(***************************************************************************)
(* Two acceptors that vote in the same ballot vote for the same value.     *)
(***************************************************************************)
LEMMA VotedOnce ==
  MsgInv => \A a1, a2, b, v1, v2 :
              VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
PROOF
  <1> SUFFICES ASSUME MsgInv,
                      NEW a1, NEW a2, NEW b, NEW v1, NEW v2,
                      VotedForIn(a1, v1, b), VotedForIn(a2, v2, b)
               PROVE  v1 = v2
    OBVIOUS
  <1>1. PICK m1 \in sent : m1.type = "2b" /\ m1.val = v1 /\ m1.bal = b /\ m1.acc = a1
    BY DEF VotedForIn
  <1>2. PICK m2 \in sent : m2.type = "2b" /\ m2.val = v2 /\ m2.bal = b /\ m2.acc = a2
    BY DEF VotedForIn
  <1>3. PICK ma1 \in sent : ma1.type = "2a" /\ ma1.bal = b /\ ma1.val = v1
    BY <1>1 DEF MsgInv
  <1>4. PICK ma2 \in sent : ma2.type = "2a" /\ ma2.bal = b /\ ma2.val = v2
    BY <1>2 DEF MsgInv
  <1>5. ma2 = ma1 BY <1>3, <1>4 DEF MsgInv
  <1> QED BY <1>3, <1>4, <1>5

(***************************************************************************)
(* If an acceptor voted for v in ballot b, then SafeAt(v, b) holds.        *)
(***************************************************************************)
LEMMA VotedInv ==
  MsgInv => \A a, v, b : VotedForIn(a, v, b) => SafeAt(v, b)
PROOF
  <1> SUFFICES ASSUME MsgInv, NEW a, NEW v, NEW b, VotedForIn(a, v, b)
               PROVE  SafeAt(v, b)
    OBVIOUS
  <1>1. PICK m \in sent : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a
    BY DEF VotedForIn
  <1>2. PICK ma \in sent : ma.type = "2a" /\ ma.bal = b /\ ma.val = v
    BY <1>1 DEF MsgInv
  <1> QED BY <1>2 DEF MsgInv

(***************************************************************************)
(* Every step either leaves sent unchanged or adds a single message.       *)
(***************************************************************************)
LEMMA NextSend ==
  ASSUME [Next]_vars
  PROVE  \/ sent' = sent
         \/ \E mm : sent' = sent \cup {mm}
PROOF
  <1>1. CASE Next
    BY <1>1 DEF Next, Phase1a, Phase1b, Phase2a, Phase2b, Send
  <1>2. CASE vars' = vars
    BY <1>2 DEF vars
  <1> QED BY <1>1, <1>2

LEMMA Next_subset ==
  ASSUME [Next]_vars
  PROVE  sent \subseteq sent'
PROOF
  <1>1. \/ sent' = sent \/ \E mm : sent' = sent \cup {mm} BY NextSend
  <1> QED BY <1>1

(***************************************************************************)
(* Characterization of VotedForIn after adding one message.               *)
(***************************************************************************)
LEMMA VotedForIn_Send ==
  ASSUME NEW mm, sent' = sent \cup {mm}, NEW a, NEW v, NEW b
  PROVE  VotedForIn(a, v, b)' <=>
            \/ VotedForIn(a, v, b)
            \/ (mm.type = "2b" /\ mm.val = v /\ mm.bal = b /\ mm.acc = a)
PROOF BY DEF VotedForIn

LEMMA VotedForIn_mono ==
  ASSUME [Next]_vars, NEW a, NEW v, NEW b, VotedForIn(a, v, b)
  PROVE  VotedForIn(a, v, b)'
PROOF BY Next_subset DEF VotedForIn

(***************************************************************************)
(* Typing of message fields.                                               *)
(***************************************************************************)
LEMMA TypeOKMsg ==
  ASSUME TypeOK, NEW m \in sent
  PROVE  /\ m.bal \in Ballots
         /\ m.type \in {"1a", "1b", "2a", "2b"}
         /\ (m.type = "1b" =>
                m.maxVBal \in Ballots \cup {-1} /\ m.maxVal \in Values \cup {None}
                /\ m.acc \in Acceptors)
         /\ (m.type = "2a" => m.val \in Values)
         /\ (m.type = "2b" => m.val \in Values /\ m.acc \in Acceptors)
PROOF BY DEF TypeOK, Messages

(***************************************************************************)
(* WontVoteIn is stable: once it holds it keeps holding.                   *)
(***************************************************************************)
LEMMA WontVoteIn_stable ==
  ASSUME TypeOK, [Next]_vars, NEW aa \in Acceptors, NEW bb \in Ballots,
         WontVoteIn(aa, bb)
  PROVE  WontVoteIn(aa, bb)'
PROOF
  <1> USE DEF Ballots
  <1>1. PICK m0 \in sent : m0.type \in {"1b", "2b"} /\ m0.acc = aa /\ m0.bal > bb
    BY DEF WontVoteIn
  <1>2. \E m \in sent' : m.type \in {"1b", "2b"} /\ m.acc = aa /\ m.bal > bb
    BY <1>1, Next_subset
  <1>3. \A v \in Values : ~ VotedForIn(aa, v, bb)
    BY DEF WontVoteIn
  <1> SUFFICES \A v \in Values : ~ VotedForIn(aa, v, bb)'
    BY <1>2 DEF WontVoteIn
  <1> SUFFICES ASSUME NEW v \in Values, VotedForIn(aa, v, bb)'
               PROVE  FALSE
    OBVIOUS
  <1>4. PICK m \in sent' : m.type = "2b" /\ m.val = v /\ m.bal = bb /\ m.acc = aa
    BY DEF VotedForIn
  <1>5. m \notin sent
    BY <1>4, <1>3 DEF VotedForIn
  <1>6. Next
    BY <1>4, <1>5 DEF vars
  <1>7. m0.bal \in Nat BY <1>1, TypeOKMsg
  <1> SUFFICES ASSUME \E ac \in Acceptors : Phase2b(ac)
               PROVE  FALSE
    <2>1. CASE \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
      BY <2>1, <1>4, <1>5 DEF Phase1a, Phase2a, Send
    <2>2. CASE \E a \in Acceptors : Phase1b(a)
      BY <2>2, <1>4, <1>5 DEF Phase1b, Send
    <2> QED BY <1>6, <2>1, <2>2 DEF Next
  <1>8. PICK ac \in Acceptors : Phase2b(ac) OBVIOUS
  <1>9. PICK mp \in sent :
            /\ mp.type = "2a"
            /\ \A m2 \in sent : m2.type \in {"1b", "2b"} /\ m2.acc = ac => mp.bal >= m2.bal
            /\ sent' = sent \cup {[type |-> "2b", bal |-> mp.bal, val |-> mp.val, acc |-> ac]}
    BY <1>8 DEF Phase2b, Send
  <1>10. m = [type |-> "2b", bal |-> mp.bal, val |-> mp.val, acc |-> ac]
    BY <1>4, <1>5, <1>9
  <1>11. ac = aa /\ mp.bal = bb
    BY <1>10, <1>4
  <1>12. mp.bal >= m0.bal
    BY <1>9, <1>1, <1>11
  <1> QED BY <1>11, <1>12, <1>1, <1>7

(***************************************************************************)
(* SafeAt is stable.                                                       *)
(***************************************************************************)
LEMMA SafeAt_stable ==
  ASSUME TypeOK, [Next]_vars, NEW v, NEW b \in Ballots, SafeAt(v, b)
  PROVE  SafeAt(v, b)'
PROOF
  <1> USE DEF Ballots
  <1> SUFFICES ASSUME NEW b2 \in 0..(b-1)
               PROVE  \E Q \in Quorums :
                        \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
    BY DEF SafeAt
  <1>1. b2 \in Ballots
    OBVIOUS
  <1>2. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
    BY DEF SafeAt
  <1> WITNESS Q \in Quorums
  <1> SUFFICES ASSUME NEW a \in Q
               PROVE  VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
    OBVIOUS
  <1>3. a \in Acceptors
    BY QuorumAssumption
  <1>4. VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
    BY <1>2
  <1>5. CASE VotedForIn(a, v, b2)
    BY <1>5, VotedForIn_mono
  <1>6. CASE WontVoteIn(a, b2)
    BY <1>6, <1>1, <1>3, WontVoteIn_stable
  <1> QED BY <1>4, <1>5, <1>6

(***************************************************************************)
(* The initial state satisfies the invariant.                              *)
(***************************************************************************)
LEMMA InitInv == Init => Inv
PROOF BY DEF Init, Inv, TypeOK, MsgInv

(***************************************************************************)
(* Core consistency argument across ballots.                              *)
(***************************************************************************)
LEMMA Main ==
  ASSUME TypeOK, MsgInv,
         NEW v1 \in Values, NEW v2 \in Values,
         NEW b1 \in Ballots, NEW b2 \in Ballots,
         b1 =< b2, ChosenIn(v1, b1), ChosenIn(v2, b2)
  PROVE  v1 = v2
PROOF
  <1> USE DEF Ballots
  <1>1. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
    BY DEF ChosenIn
  <1>2. PICK a2 \in Q2 : TRUE
    BY QuorumNonEmpty
  <1>3. VotedForIn(a2, v2, b2)
    BY <1>1, <1>2
  <1>4. SafeAt(v2, b2)
    BY <1>3, VotedInv
  <1>5. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
    BY DEF ChosenIn
  <1>6. CASE b1 = b2
    <2>1. PICK a \in Acceptors : a \in Q1 /\ a \in Q2
      BY QuorumIntersect
    <2>2. VotedForIn(a, v1, b1)
      BY <1>5, <2>1
    <2>3. VotedForIn(a, v2, b2)
      BY <1>1, <2>1
    <2> QED BY <2>2, <2>3, <1>6, VotedOnce
  <1>7. CASE b1 # b2
    <2>0. b1 < b2
      BY <1>7
    <2>1. b1 \in 0..(b2-1)
      BY <2>0
    <2>2. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
      BY <1>4, <2>1 DEF SafeAt
    <2>3. PICK a \in Acceptors : a \in Q /\ a \in Q1
      BY QuorumIntersect
    <2>4. VotedForIn(a, v1, b1)
      BY <1>5, <2>3
    <2>5. VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
      BY <2>2, <2>3
    <2>6. ~ WontVoteIn(a, b1)
      BY <2>4 DEF WontVoteIn
    <2>7. VotedForIn(a, v2, b1)
      BY <2>5, <2>6
    <2> QED BY <2>4, <2>7, VotedOnce
  <1> QED BY <1>6, <1>7

(***************************************************************************)
(* The invariant implies the consistency property.                        *)
(***************************************************************************)
LEMMA InvConsistency == Inv => Consistency
PROOF
  <1> USE DEF Ballots
  <1> SUFFICES ASSUME TypeOK, MsgInv,
                      NEW v1 \in Values, NEW v2 \in Values,
                      Chosen(v1), Chosen(v2)
               PROVE  v1 = v2
    BY DEF Inv, Consistency
  <1>1. PICK b1 \in Ballots : ChosenIn(v1, b1) BY DEF Chosen
  <1>2. PICK b2 \in Ballots : ChosenIn(v2, b2) BY DEF Chosen
  <1>3. b1 =< b2 \/ b2 =< b1 BY <1>1, <1>2
  <1>4. CASE b1 =< b2
    BY <1>1, <1>2, <1>4, Main
  <1>5. CASE b2 =< b1
    <2>1. v2 = v1 BY <1>1, <1>2, <1>5, Main
    <2> QED BY <2>1
  <1> QED BY <1>3, <1>4, <1>5

(***************************************************************************)
(* Typing of elements returned by last_voted.                              *)
(***************************************************************************)
LEMMA last_votedType ==
  ASSUME TypeOK, NEW a \in Acceptors, NEW r \in last_voted(a)
  PROVE  r.bal \in Ballots \cup {-1} /\ r.val \in Values \cup {None}
PROOF
  <1>1. CASE {mm \in sent : mm.type = "2b" /\ mm.acc = a} # {}
    <2>1. r \in {mm \in sent : mm.type = "2b" /\ mm.acc = a}
      BY <1>1 DEF last_voted
    <2> QED BY <2>1, TypeOKMsg
  <1>2. CASE {mm \in sent : mm.type = "2b" /\ mm.acc = a} = {}
    <2>1. r = [bal |-> -1, val |-> None] BY <1>2 DEF last_voted
    <2> QED BY <2>1
  <1> QED BY <1>1, <1>2

(***************************************************************************)
(* If the added message is not a 2b message, no new vote is created.       *)
(***************************************************************************)
LEMMA NoNewVote ==
  ASSUME NEW mm, sent' = sent \cup {mm}, mm.type # "2b",
         NEW a, NEW v, NEW b, VotedForIn(a, v, b)'
  PROVE  VotedForIn(a, v, b)
PROOF BY DEF VotedForIn

(***************************************************************************)
(* TypeOK is inductive.                                                    *)
(***************************************************************************)
LEMMA NextTypeOK ==
  ASSUME TypeOK, [Next]_vars
  PROVE  TypeOK'
PROOF
  <1> USE DEF Ballots
  <1> SUFFICES ASSUME Next PROVE TypeOK'
    BY DEF vars, TypeOK
  <1>1. CASE \E b \in Ballots : Phase1a(b)
    <2> PICK b \in Ballots : Phase1a(b) BY <1>1
    <2>1. sent' = sent \cup {[type |-> "1a", bal |-> b]} BY DEF Phase1a, Send
    <2>2. [type |-> "1a", bal |-> b] \in Messages BY DEF Messages
    <2> QED BY <2>1, <2>2 DEF TypeOK
  <1>2. CASE \E a \in Acceptors : Phase1b(a)
    <2> PICK a \in Acceptors : Phase1b(a) BY <1>2
    <2>1. PICK mm \in sent, r \in last_voted(a) :
            /\ mm.type = "1a"
            /\ sent' = sent \cup {[type |-> "1b", bal |-> mm.bal, maxVBal |-> r.bal,
                                   maxVal |-> r.val, acc |-> a]}
      BY DEF Phase1b, Send
    <2>2. mm.bal \in Ballots BY <2>1, TypeOKMsg
    <2>3. r.bal \in Ballots \cup {-1} /\ r.val \in Values \cup {None}
      BY <2>1, last_votedType
    <2>4. [type |-> "1b", bal |-> mm.bal, maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a] \in Messages
      BY <2>2, <2>3 DEF Messages
    <2> QED BY <2>1, <2>4 DEF TypeOK
  <1>3. CASE \E b \in Ballots : Phase2a(b)
    <2> PICK b \in Ballots : Phase2a(b) BY <1>3
    <2>1. PICK v \in Values : sent' = sent \cup {[type |-> "2a", bal |-> b, val |-> v]}
      BY DEF Phase2a, Send
    <2>2. [type |-> "2a", bal |-> b, val |-> v] \in Messages BY DEF Messages
    <2> QED BY <2>1, <2>2 DEF TypeOK
  <1>4. CASE \E a \in Acceptors : Phase2b(a)
    <2> PICK a \in Acceptors : Phase2b(a) BY <1>4
    <2>1. PICK mm \in sent :
            /\ mm.type = "2a"
            /\ sent' = sent \cup {[type |-> "2b", bal |-> mm.bal, val |-> mm.val, acc |-> a]}
      BY DEF Phase2b, Send
    <2>2. mm.bal \in Ballots /\ mm.val \in Values BY <2>1, TypeOKMsg
    <2>3. [type |-> "2b", bal |-> mm.bal, val |-> mm.val, acc |-> a] \in Messages
      BY <2>2 DEF Messages
    <2> QED BY <2>1, <2>3 DEF TypeOK
  <1> QED BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* The non-action-specific parts of MsgInv are preserved for old messages. *)
(***************************************************************************)
LEMMA OldMsgPreserved ==
  ASSUME TypeOK, MsgInv, [Next]_vars, NEW m \in sent
  PROVE  /\ (m.type = "1b" => (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1))
         /\ (m.type = "2a" => SafeAt(m.val, m.bal)')
         /\ (m.type = "2b" =>
                \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val)
PROOF
  <1>1. m.bal \in Ballots BY TypeOKMsg
  <1>2. m.type = "1b" => (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
    <2> SUFFICES ASSUME m.type = "1b"
                 PROVE  VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
      OBVIOUS
    <2>1. VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1 BY DEF MsgInv
    <2>2. CASE VotedForIn(m.acc, m.maxVal, m.maxVBal) BY <2>2, VotedForIn_mono
    <2> QED BY <2>1, <2>2
  <1>3. m.type = "2a" => SafeAt(m.val, m.bal)'
    <2> SUFFICES ASSUME m.type = "2a" PROVE SafeAt(m.val, m.bal)'
      OBVIOUS
    <2>1. SafeAt(m.val, m.bal) BY DEF MsgInv
    <2> QED BY <2>1, <1>1, SafeAt_stable
  <1>4. m.type = "2b" =>
            \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
    <2> SUFFICES ASSUME m.type = "2b"
                 PROVE  \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
      OBVIOUS
    <2>1. PICK m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
      BY DEF MsgInv
    <2>2. m2 \in sent' BY <2>1, Next_subset
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>2, <1>3, <1>4

(***************************************************************************)
(* The crux: the value selected in Phase2a is SafeAt the ballot.           *)
(***************************************************************************)
LEMMA Phase2aSafeAt ==
  ASSUME TypeOK, MsgInv,
         NEW b \in Ballots, NEW v \in Values, NEW Q \in Quorums,
         NEW S \in SUBSET {mm \in sent : mm.type = "1b" /\ mm.bal = b},
         \A a \in Q : \E mm \in S : mm.acc = a,
         \/ \A mm \in S : mm.maxVBal = -1
         \/ \E c \in 0..(b-1) : /\ \A mm \in S : mm.maxVBal =< c
                                /\ \E mm \in S : mm.maxVBal = c /\ mm.maxVal = v
  PROVE  SafeAt(v, b)
PROOF
  <1> USE DEF Ballots
  <1>cover. \A a \in Q : \E mm \in S : mm.acc = a OBVIOUS
  <1>Ssub. \A mm \in S : mm \in sent /\ mm.type = "1b" /\ mm.bal = b OBVIOUS
  <1>Qacc. Q \subseteq Acceptors BY QuorumAssumption
  <1> SUFFICES ASSUME NEW b2 \in 0..(b-1)
               PROVE  \E QQ \in Quorums : \A a \in QQ : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
    BY DEF SafeAt
  <1>b2. b2 \in Nat /\ b2 < b /\ 0 =< b2 BY DEF Ballots
  <1>1. CASE \A mm \in S : mm.maxVBal = -1
    <2> WITNESS Q \in Quorums
    <2> SUFFICES ASSUME NEW a \in Q
                 PROVE  VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
      OBVIOUS
    <2>1. PICK mm \in S : mm.acc = a BY <1>cover
    <2>2. mm \in sent /\ mm.type = "1b" /\ mm.bal = b /\ mm.maxVBal = -1
      BY <2>1, <1>1, <1>Ssub
    <2>3. \A bb \in mm.maxVBal+1 .. mm.bal-1 : ~\E vv \in Values : VotedForIn(mm.acc, vv, bb)
      BY <2>2 DEF MsgInv
    <2>4. b2 \in mm.maxVBal+1 .. mm.bal-1 BY <2>2, <1>b2
    <2>5. \A vv \in Values : ~ VotedForIn(a, vv, b2) BY <2>3, <2>4, <2>1
    <2>6. \E msg \in sent : msg.type \in {"1b", "2b"} /\ msg.acc = a /\ msg.bal > b2
      BY <2>2, <2>1, <1>b2
    <2> QED BY <2>5, <2>6 DEF WontVoteIn
  <1>2. CASE \E c \in 0..(b-1) : /\ \A mm \in S : mm.maxVBal =< c
                                 /\ \E mm \in S : mm.maxVBal = c /\ mm.maxVal = v
    <2>1. PICK c \in 0..(b-1) : /\ \A mm \in S : mm.maxVBal =< c
                               /\ \E mm \in S : mm.maxVBal = c /\ mm.maxVal = v
      BY <1>2
    <2>c. c \in Nat /\ 0 =< c /\ c < b BY <2>1
    <2>2. PICK mc \in S : mc.maxVBal = c /\ mc.maxVal = v BY <2>1
    <2>3. mc \in sent /\ mc.type = "1b" /\ mc.bal = b BY <2>2, <1>Ssub
    <2>4. VotedForIn(mc.acc, v, c)
      <3>1. VotedForIn(mc.acc, mc.maxVal, mc.maxVBal) \/ mc.maxVBal = -1
        BY <2>3 DEF MsgInv
      <3> QED BY <3>1, <2>2, <2>c
    <2>5. SafeAt(v, c) BY <2>4, VotedInv
    <2>6. CASE b2 \in 0..(c-1)
      <3>1. \A b3 \in 0..(c-1) :
              \E QQ \in Quorums : \A a \in QQ : VotedForIn(a, v, b3) \/ WontVoteIn(a, b3)
        BY <2>5 DEF SafeAt
      <3> QED BY <3>1, <2>6
    <2>7. CASE b2 \in c..(b-1)
      <3> WITNESS Q \in Quorums
      <3> SUFFICES ASSUME NEW a \in Q
                   PROVE  VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
        OBVIOUS
      <3>1. PICK mm \in S : mm.acc = a BY <1>cover
      <3>2. mm \in sent /\ mm.type = "1b" /\ mm.bal = b /\ mm.maxVBal =< c
        BY <3>1, <2>1, <1>Ssub
      <3>3. mm.maxVBal \in Ballots \cup {-1} BY <3>2, TypeOKMsg
      <3>b2c. c =< b2 /\ b2 < b BY <2>7, <1>b2
      <3>4. CASE mm.maxVBal = b2
        <4>1. b2 = c BY <3>4, <3>2, <3>b2c, <2>c, <3>3
        <4>2. VotedForIn(a, mm.maxVal, b2)
          <5>1. VotedForIn(mm.acc, mm.maxVal, mm.maxVBal) \/ mm.maxVBal = -1
            BY <3>2 DEF MsgInv
          <5>2. mm.maxVBal # -1 BY <3>4, <3>b2c, <2>c
          <5> QED BY <5>1, <5>2, <3>4, <3>1
        <4>3. VotedForIn(mc.acc, v, b2) BY <2>4, <4>1
        <4>4. mm.maxVal = v BY <4>2, <4>3, VotedOnce
        <4> QED BY <4>2, <4>4
      <3>5. CASE mm.maxVBal # b2
        <4>1. mm.maxVBal < b2 BY <3>5, <3>2, <3>b2c, <3>3, <2>c
        <4>2. b2 \in mm.maxVBal+1 .. mm.bal-1 BY <4>1, <3>2, <3>b2c, <3>3
        <4>3. \A bb \in mm.maxVBal+1 .. mm.bal-1 : ~\E vv \in Values : VotedForIn(mm.acc, vv, bb)
          BY <3>2 DEF MsgInv
        <4>4. \A vv \in Values : ~ VotedForIn(a, vv, b2) BY <4>2, <4>3, <3>1
        <4>5. \E msg \in sent : msg.type \in {"1b", "2b"} /\ msg.acc = a /\ msg.bal > b2
          BY <3>2, <3>1, <3>b2c
        <4> QED BY <4>4, <4>5 DEF WontVoteIn
      <3> QED BY <3>4, <3>5
    <2> QED BY <2>6, <2>7, <2>c, <1>b2
  <1> QED BY <1>1, <1>2

(***************************************************************************)
(* The MsgInv condition for a single message, factored out.                *)
(***************************************************************************)
MsgInvFor(m) ==
    /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                        /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
    /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                        /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
    /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                         /\ m2.bal  = m.bal
                                         /\ m2.val  = m.val

LEMMA MsgInvForDef == MsgInv <=> \A m \in sent : MsgInvFor(m)
BY DEF MsgInv, MsgInvFor

(***************************************************************************)
(* Phase1a preserves MsgInv.                                               *)
(***************************************************************************)
LEMMA Phase1aInv ==
  ASSUME Inv, NEW b0 \in Ballots, Phase1a(b0)
  PROVE  MsgInv'
PROOF
  <1> USE DEF Ballots
  <1>tok. TypeOK BY DEF Inv
  <1>minv. MsgInv BY DEF Inv
  <1>n1. Next BY DEF Next
  <1>n2. [Next]_vars BY <1>n1
  <1> DEFINE nm == [type |-> "1a", bal |-> b0]
  <1>def. sent' = sent \cup {nm} BY DEF Phase1a, Send
  <1>nt. nm.type = "1a" OBVIOUS
  <1> SUFFICES ASSUME NEW m \in sent' PROVE MsgInvFor(m)'
    BY DEF MsgInv, MsgInvFor
  <1>old. CASE m \in sent
    <2>1. m.type = "1b" =>
              /\ (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
              /\ \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
      <3> SUFFICES ASSUME m.type = "1b"
                   PROVE  /\ (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
                          /\ \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
        OBVIOUS
      <3>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
        BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
      <3>2. \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
        <4> SUFFICES ASSUME NEW b \in m.maxVBal+1..m.bal-1, NEW v \in Values,
                            VotedForIn(m.acc, v, b)'
                     PROVE  FALSE
          OBVIOUS
        <4>1. VotedForIn(m.acc, v, b) BY <1>def, <1>nt, NoNewVote
        <4>2. \A bb \in m.maxVBal+1..m.bal-1 : ~\E vv \in Values : VotedForIn(m.acc, vv, bb)
          BY <1>old, <1>minv DEF MsgInv
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2
    <2>2. m.type = "2a" =>
              /\ SafeAt(m.val, m.bal)'
              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
      <3> SUFFICES ASSUME m.type = "2a"
                   PROVE  /\ SafeAt(m.val, m.bal)'
                          /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        OBVIOUS
      <3>1. SafeAt(m.val, m.bal)'
        BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
      <3>2. \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        <4> SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
                     PROVE  m2 = m
          OBVIOUS
        <4>1. CASE m2 \in sent BY <4>1, <1>old, <1>minv DEF MsgInv
        <4>2. CASE m2 = nm BY <4>2, <1>nt
        <4> QED BY <4>1, <4>2, <1>def
      <3> QED BY <3>1, <3>2
    <2>3. m.type = "2b" =>
              \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
      BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
    <2> QED BY <2>1, <2>2, <2>3 DEF MsgInvFor
  <1>new. CASE m = nm
    BY <1>new, <1>nt DEF MsgInvFor
  <1> QED BY <1>old, <1>new, <1>def

(***************************************************************************)
(* last_voted returns an actual vote (or the default -1 entry).            *)
(***************************************************************************)
LEMMA last_votedVote ==
  ASSUME TypeOK, NEW a \in Acceptors, NEW r \in last_voted(a)
  PROVE  VotedForIn(a, r.val, r.bal) \/ r.bal = -1
PROOF
  <1>1. CASE {mm \in sent : mm.type = "2b" /\ mm.acc = a} # {}
    <2>1. r \in {mm \in sent : mm.type = "2b" /\ mm.acc = a} BY <1>1 DEF last_voted
    <2>2. r \in sent /\ r.type = "2b" /\ r.acc = a BY <2>1
    <2> QED BY <2>2 DEF VotedForIn
  <1>2. CASE {mm \in sent : mm.type = "2b" /\ mm.acc = a} = {}
    <2>1. r = [bal |-> -1, val |-> None] BY <1>2 DEF last_voted
    <2> QED BY <2>1
  <1> QED BY <1>1, <1>2

(***************************************************************************)
(* last_voted returns the maximum ballot the acceptor has voted in.        *)
(***************************************************************************)
LEMMA last_votedMax ==
  ASSUME TypeOK, NEW a \in Acceptors, NEW r \in last_voted(a),
         NEW v, NEW b, VotedForIn(a, v, b)
  PROVE  b =< r.bal
PROOF
  <1> USE DEF Ballots
  <1>1. PICK msg \in sent : msg.type = "2b" /\ msg.val = v /\ msg.bal = b /\ msg.acc = a
    BY DEF VotedForIn
  <1>2. msg \in {mm \in sent : mm.type = "2b" /\ mm.acc = a} BY <1>1
  <1>3. {mm \in sent : mm.type = "2b" /\ mm.acc = a} # {} BY <1>2
  <1>4. /\ r \in {mm \in sent : mm.type = "2b" /\ mm.acc = a}
        /\ \A m2 \in {mm \in sent : mm.type = "2b" /\ mm.acc = a} : r.bal >= m2.bal
    BY <1>3 DEF last_voted
  <1>5. r.bal >= msg.bal BY <1>4, <1>2
  <1>6. r.bal \in Nat /\ b \in Nat BY <1>4, <1>1, TypeOKMsg
  <1> QED BY <1>5, <1>1, <1>6

(***************************************************************************)
(* Phase1b preserves MsgInv.                                               *)
(***************************************************************************)
LEMMA Phase1bInv ==
  ASSUME Inv, NEW a0 \in Acceptors, Phase1b(a0)
  PROVE  MsgInv'
PROOF
  <1> USE DEF Ballots
  <1>tok. TypeOK BY DEF Inv
  <1>minv. MsgInv BY DEF Inv
  <1>n1. Next BY DEF Next
  <1>n2. [Next]_vars BY <1>n1
  <1>p. PICK mp \in sent, r \in last_voted(a0) :
          sent' = sent \cup {[type |-> "1b", bal |-> mp.bal, maxVBal |-> r.bal,
                              maxVal |-> r.val, acc |-> a0]}
    BY DEF Phase1b, Send
  <1> DEFINE nm == [type |-> "1b", bal |-> mp.bal, maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a0]
  <1>def. sent' = sent \cup {nm} BY <1>p
  <1>nt. nm.type = "1b" /\ nm.acc = a0 /\ nm.bal = mp.bal /\ nm.maxVBal = r.bal /\ nm.maxVal = r.val
    OBVIOUS
  <1> SUFFICES ASSUME NEW m \in sent' PROVE MsgInvFor(m)'
    BY DEF MsgInv, MsgInvFor
  <1>old. CASE m \in sent
    <2>1. m.type = "1b" =>
              /\ (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
              /\ \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
      <3> SUFFICES ASSUME m.type = "1b"
                   PROVE  /\ (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
                          /\ \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
        OBVIOUS
      <3>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
        BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
      <3>2. \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
        <4> SUFFICES ASSUME NEW b \in m.maxVBal+1..m.bal-1, NEW v \in Values,
                            VotedForIn(m.acc, v, b)'
                     PROVE  FALSE
          OBVIOUS
        <4>1. VotedForIn(m.acc, v, b) BY <1>def, <1>nt, NoNewVote
        <4>2. \A bb \in m.maxVBal+1..m.bal-1 : ~\E vv \in Values : VotedForIn(m.acc, vv, bb)
          BY <1>old, <1>minv DEF MsgInv
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2
    <2>2. m.type = "2a" =>
              /\ SafeAt(m.val, m.bal)'
              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
      <3> SUFFICES ASSUME m.type = "2a"
                   PROVE  /\ SafeAt(m.val, m.bal)'
                          /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        OBVIOUS
      <3>1. SafeAt(m.val, m.bal)'
        BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
      <3>2. \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        <4> SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
                     PROVE  m2 = m
          OBVIOUS
        <4>1. CASE m2 \in sent BY <4>1, <1>old, <1>minv DEF MsgInv
        <4>2. CASE m2 = nm BY <4>2, <1>nt
        <4> QED BY <4>1, <4>2, <1>def
      <3> QED BY <3>1, <3>2
    <2>3. m.type = "2b" =>
              \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
      BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
    <2> QED BY <2>1, <2>2, <2>3 DEF MsgInvFor
  <1>new. CASE m = nm
    <2> SUFFICES MsgInvFor(nm)' BY <1>new
    <2> SUFFICES /\ (VotedForIn(nm.acc, nm.maxVal, nm.maxVBal)' \/ nm.maxVBal = -1)
                 /\ \A b \in nm.maxVBal+1..nm.bal-1 : ~\E v \in Values : VotedForIn(nm.acc, v, b)'
      BY <1>nt DEF MsgInvFor
    <2>1. VotedForIn(nm.acc, nm.maxVal, nm.maxVBal)' \/ nm.maxVBal = -1
      <3>1. VotedForIn(a0, r.val, r.bal) \/ r.bal = -1 BY <1>p, <1>tok, last_votedVote
      <3>2. CASE VotedForIn(a0, r.val, r.bal)
        <4>1. VotedForIn(a0, r.val, r.bal)' BY <3>2, <1>n2, VotedForIn_mono
        <4> QED BY <4>1, <1>nt
      <3>3. CASE r.bal = -1 BY <3>3, <1>nt
      <3> QED BY <3>1, <3>2, <3>3
    <2>2. \A b \in nm.maxVBal+1..nm.bal-1 : ~\E v \in Values : VotedForIn(nm.acc, v, b)'
      <3> SUFFICES ASSUME NEW b \in nm.maxVBal+1..nm.bal-1, NEW v \in Values,
                          VotedForIn(nm.acc, v, b)'
                   PROVE  FALSE
        OBVIOUS
      <3>1. VotedForIn(a0, v, b) BY <1>def, <1>nt, NoNewVote
      <3>2. b =< r.bal BY <3>1, <1>p, <1>tok, last_votedMax
      <3>r. r.bal \in Ballots \cup {-1} BY <1>p, <1>tok, last_votedType
      <3> QED BY <3>2, <3>r, <1>nt
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>old, <1>new, <1>def

(***************************************************************************)
(* Phase2b preserves MsgInv.                                               *)
(***************************************************************************)
LEMMA Phase2bInv ==
  ASSUME Inv, NEW a0 \in Acceptors, Phase2b(a0)
  PROVE  MsgInv'
PROOF
  <1> USE DEF Ballots
  <1>tok. TypeOK BY DEF Inv
  <1>minv. MsgInv BY DEF Inv
  <1>n1. Next BY DEF Next
  <1>n2. [Next]_vars BY <1>n1
  <1>p. PICK mp \in sent :
          /\ mp.type = "2a"
          /\ \A m2 \in sent : m2.type \in {"1b", "2b"} /\ m2.acc = a0 => mp.bal >= m2.bal
          /\ sent' = sent \cup {[type |-> "2b", bal |-> mp.bal, val |-> mp.val, acc |-> a0]}
    BY DEF Phase2b, Send
  <1> DEFINE nm == [type |-> "2b", bal |-> mp.bal, val |-> mp.val, acc |-> a0]
  <1>def. sent' = sent \cup {nm} BY <1>p
  <1>nt. nm.type = "2b" /\ nm.acc = a0 /\ nm.bal = mp.bal /\ nm.val = mp.val
    OBVIOUS
  <1> SUFFICES ASSUME NEW m \in sent' PROVE MsgInvFor(m)'
    BY DEF MsgInv, MsgInvFor
  <1>old. CASE m \in sent
    <2>1. m.type = "1b" =>
              /\ (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
              /\ \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
      <3> SUFFICES ASSUME m.type = "1b"
                   PROVE  /\ (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
                          /\ \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
        OBVIOUS
      <3>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
        BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
      <3>2. \A b \in m.maxVBal+1..m.bal-1 : ~\E v \in Values : VotedForIn(m.acc, v, b)'
        <4> SUFFICES ASSUME NEW b \in m.maxVBal+1..m.bal-1, NEW v \in Values,
                            VotedForIn(m.acc, v, b)'
                     PROVE  FALSE
          OBVIOUS
        <4>1. \A bb \in m.maxVBal+1..m.bal-1 : ~\E vv \in Values : VotedForIn(m.acc, vv, bb)
          BY <1>old, <1>minv DEF MsgInv
        <4>2. VotedForIn(m.acc, v, b) \/ (nm.acc = m.acc /\ nm.val = v /\ nm.bal = b)
          BY <1>def, <1>nt, VotedForIn_Send
        <4>3. CASE VotedForIn(m.acc, v, b) BY <4>3, <4>1
        <4>4. CASE nm.acc = m.acc /\ nm.val = v /\ nm.bal = b
          <5>1. m.acc = a0 /\ b = mp.bal BY <4>4, <1>nt
          <5>2. mp.bal >= m.bal BY <1>p, <5>1, <1>old
          <5>3. m.bal \in Ballots /\ mp.bal \in Ballots BY <1>old, <1>p, <1>tok, TypeOKMsg
          <5> QED BY <5>1, <5>2, <5>3
        <4> QED BY <4>2, <4>3, <4>4
      <3> QED BY <3>1, <3>2
    <2>2. m.type = "2a" =>
              /\ SafeAt(m.val, m.bal)'
              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
      <3> SUFFICES ASSUME m.type = "2a"
                   PROVE  /\ SafeAt(m.val, m.bal)'
                          /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        OBVIOUS
      <3>1. SafeAt(m.val, m.bal)'
        BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
      <3>2. \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        <4> SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
                     PROVE  m2 = m
          OBVIOUS
        <4>1. CASE m2 \in sent BY <4>1, <1>old, <1>minv DEF MsgInv
        <4>2. CASE m2 = nm BY <4>2, <1>nt
        <4> QED BY <4>1, <4>2, <1>def
      <3> QED BY <3>1, <3>2
    <2>3. m.type = "2b" =>
              \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
      BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
    <2> QED BY <2>1, <2>2, <2>3 DEF MsgInvFor
  <1>new. CASE m = nm
    <2> SUFFICES MsgInvFor(nm)' BY <1>new
    <2> SUFFICES \E m2 \in sent' : m2.type = "2a" /\ m2.bal = nm.bal /\ m2.val = nm.val
      BY <1>nt DEF MsgInvFor
    <2>1. mp \in sent' BY <1>def
    <2> QED BY <2>1, <1>p, <1>nt
  <1> QED BY <1>old, <1>new, <1>def

(***************************************************************************)
(* Phase2a preserves MsgInv.                                               *)
(***************************************************************************)
LEMMA Phase2aInv ==
  ASSUME Inv, NEW b0 \in Ballots, Phase2a(b0)
  PROVE  MsgInv'
PROOF
  <1> USE DEF Ballots
  <1>tok. TypeOK BY DEF Inv
  <1>minv. MsgInv BY DEF Inv
  <1>n1. Next BY DEF Next
  <1>n2. [Next]_vars BY <1>n1
  <1>pre. ~\E mm \in sent : mm.type = "2a" /\ mm.bal = b0 BY DEF Phase2a
  <1>p. PICK v \in Values, Q \in Quorums,
             S \in SUBSET {mm \in sent : mm.type = "1b" /\ mm.bal = b0} :
          /\ \A a \in Q : \E mm \in S : mm.acc = a
          /\ \/ \A mm \in S : mm.maxVBal = -1
             \/ \E c \in 0..(b0-1) : /\ \A mm \in S : mm.maxVBal =< c
                                     /\ \E mm \in S : mm.maxVBal = c /\ mm.maxVal = v
          /\ sent' = sent \cup {[type |-> "2a", bal |-> b0, val |-> v]}
    BY DEF Phase2a, Send
  <1> DEFINE nm == [type |-> "2a", bal |-> b0, val |-> v]
  <1>def. sent' = sent \cup {nm} BY <1>p
  <1>nt. nm.type = "2a" /\ nm.bal = b0 /\ nm.val = v OBVIOUS
  <1> SUFFICES ASSUME NEW m \in sent' PROVE MsgInvFor(m)'
    BY DEF MsgInv, MsgInvFor
  <1>old. CASE m \in sent
    <2>1. m.type = "1b" =>
              /\ (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
              /\ \A b \in m.maxVBal+1..m.bal-1 : ~\E v0 \in Values : VotedForIn(m.acc, v0, b)'
      <3> SUFFICES ASSUME m.type = "1b"
                   PROVE  /\ (VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1)
                          /\ \A b \in m.maxVBal+1..m.bal-1 : ~\E v0 \in Values : VotedForIn(m.acc, v0, b)'
        OBVIOUS
      <3>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
        BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
      <3>2. \A b \in m.maxVBal+1..m.bal-1 : ~\E v0 \in Values : VotedForIn(m.acc, v0, b)'
        <4> SUFFICES ASSUME NEW b \in m.maxVBal+1..m.bal-1, NEW v0 \in Values,
                            VotedForIn(m.acc, v0, b)'
                     PROVE  FALSE
          OBVIOUS
        <4>1. VotedForIn(m.acc, v0, b) BY <1>def, <1>nt, NoNewVote
        <4>2. \A bb \in m.maxVBal+1..m.bal-1 : ~\E vv \in Values : VotedForIn(m.acc, vv, bb)
          BY <1>old, <1>minv DEF MsgInv
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2
    <2>2. m.type = "2a" =>
              /\ SafeAt(m.val, m.bal)'
              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
      <3> SUFFICES ASSUME m.type = "2a"
                   PROVE  /\ SafeAt(m.val, m.bal)'
                          /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        OBVIOUS
      <3>1. SafeAt(m.val, m.bal)'
        BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
      <3>2. \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        <4> SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
                     PROVE  m2 = m
          OBVIOUS
        <4>1. CASE m2 \in sent BY <4>1, <1>old, <1>minv DEF MsgInv
        <4>2. CASE m2 = nm
          <5>1. m.bal = b0 BY <4>2, <1>nt
          <5> QED BY <5>1, <1>old, <1>pre
        <4> QED BY <4>1, <4>2, <1>def
      <3> QED BY <3>1, <3>2
    <2>3. m.type = "2b" =>
              \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
      BY <1>old, <1>n2, <1>minv, <1>tok, OldMsgPreserved
    <2> QED BY <2>1, <2>2, <2>3 DEF MsgInvFor
  <1>new. CASE m = nm
    <2> SUFFICES MsgInvFor(nm)' BY <1>new
    <2> SUFFICES /\ SafeAt(nm.val, nm.bal)'
                 /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = nm.bal) => m2 = nm
      BY <1>nt DEF MsgInvFor
    <2>1. SafeAt(v, b0) BY <1>p, <1>tok, <1>minv, Phase2aSafeAt
    <2>2. SafeAt(v, b0)' BY <2>1, <1>n2, <1>tok, SafeAt_stable
    <2>3. SafeAt(nm.val, nm.bal)' BY <2>2, <1>nt
    <2>4. \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = nm.bal) => m2 = nm
      <3> SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = nm.bal
                   PROVE  m2 = nm
        OBVIOUS
      <3>1. CASE m2 \in sent
        <4>1. m2.bal = b0 BY <3>1, <1>nt
        <4> QED BY <4>1, <3>1, <1>pre
      <3>2. CASE m2 = nm BY <3>2
      <3> QED BY <3>1, <3>2, <1>def
    <2> QED BY <2>3, <2>4
  <1> QED BY <1>old, <1>new, <1>def

(***************************************************************************)
(* A stuttering step preserves MsgInv.                                     *)
(***************************************************************************)
LEMMA StutterInv ==
  ASSUME Inv, vars' = vars
  PROVE  MsgInv'
PROOF
  <1>1. sent' = sent BY DEF vars
  <1>2. MsgInv BY DEF Inv
  <1> SUFFICES ASSUME NEW m \in sent' PROVE MsgInvFor(m)'
    BY DEF MsgInv, MsgInvFor
  <1>3. m \in sent BY <1>1
  <1>4. MsgInvFor(m) BY <1>3, <1>2, MsgInvForDef
  <1> QED BY <1>1, <1>4 DEF MsgInvFor, VotedForIn, SafeAt, WontVoteIn

(***************************************************************************)
(* Inv is inductive.                                                       *)
(***************************************************************************)
LEMMA NextInv ==
  ASSUME Inv, [Next]_vars
  PROVE  Inv'
PROOF
  <1>tok. TypeOK' BY NextTypeOK DEF Inv
  <1> SUFFICES MsgInv' BY <1>tok DEF Inv
  <1>1. CASE \E b \in Ballots : Phase1a(b)
    <2> PICK b \in Ballots : Phase1a(b) BY <1>1
    <2> QED BY Phase1aInv
  <1>2. CASE \E a \in Acceptors : Phase1b(a)
    <2> PICK a \in Acceptors : Phase1b(a) BY <1>2
    <2> QED BY Phase1bInv
  <1>3. CASE \E b \in Ballots : Phase2a(b)
    <2> PICK b \in Ballots : Phase2a(b) BY <1>3
    <2> QED BY Phase2aInv
  <1>4. CASE \E a \in Acceptors : Phase2b(a)
    <2> PICK a \in Acceptors : Phase2b(a) BY <1>4
    <2> QED BY Phase2bInv
  <1>5. CASE vars' = vars
    BY <1>5, StutterInv
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

(***************************************************************************)
(* Inv is an invariant of the specification.                              *)
(***************************************************************************)
LEMMA Invariance == Spec => []Inv
PROOF
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv' BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM Consistent == Spec => []Consistency
PROOF
  <1>1. Spec => []Inv BY Invariance
  <1>2. Inv => Consistency BY InvConsistency
  <1> QED BY <1>1, <1>2, PTL

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