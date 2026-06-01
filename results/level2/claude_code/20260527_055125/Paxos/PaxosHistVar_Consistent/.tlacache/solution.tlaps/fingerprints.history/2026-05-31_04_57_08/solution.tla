------------------------------- MODULE PaxosHistVar_Consistent --------------------------

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

Phase1a(b) == Send([type |-> "1a", bal |-> b])

last_voted(a) == LET 2bs == {m \in sent: m.type = "2b" /\ m.acc = a}
                 IN IF 2bs # {} THEN {m \in 2bs: \A m2 \in 2bs: m.bal >= m2.bal}
                    ELSE {[bal |-> -1, val |-> None]}

Phase1b(a) ==
  \E m \in sent, r \in last_voted(a):
     /\ m.type = "1a"
     /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal > m2.bal
     /\ Send([type |-> "1b", bal |-> m.bal,
              maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a])

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

Phase2b(a) ==
  \E m \in sent :
    /\ m.type = "2a"
    /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal >= m2.bal
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])

Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------

VotedForIn(a, v, b) == \E m \in sent : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
-----------------------------------------------------------------------------

(* Helper definitions for the proof of Consistency *)

DidNotVoteIn(a, b) == \A v \in Values : ~VotedForIn(a, v, b)

WontVoteIn(a, b) == /\ DidNotVoteIn(a, b)
                    /\ \E m \in sent : /\ m.type \in {"1b", "2b"}
                                       /\ m.acc = a
                                       /\ m.bal > b

SafeAt(v, b) == \A c \in 0..(b-1) :
                  \E Q \in Quorums :
                    \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, bal : Ballots,
        maxVBal : Ballots \cup {-1},
        maxVal : Values \cup {None}, acc : Acceptors]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK == sent \in SUBSET Messages

MsgInv1b(m) ==
  /\ (m.maxVBal >= 0) => /\ m.maxVal \in Values
                         /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
  /\ \A bb \in (m.maxVBal+1)..(m.bal-1) : DidNotVoteIn(m.acc, bb)

MsgInv2a(m) ==
  /\ SafeAt(m.val, m.bal)
  /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => (m2.val = m.val)

MsgInv2b(m) ==
  \E m2 \in sent : /\ m2.type = "2a"
                   /\ m2.bal = m.bal
                   /\ m2.val = m.val

MsgInv == \A m \in sent :
  /\ (m.type = "1b") => MsgInv1b(m)
  /\ (m.type = "2a") => MsgInv2a(m)
  /\ (m.type = "2b") => MsgInv2b(m)

Inv == TypeOK /\ MsgInv

-----------------------------------------------------------------------------

(* Init satisfies Inv *)
LEMMA InitImpliesInv == Init => Inv
  <1>1. SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>2. sent = {}  BY <1>1 DEF Init
  <1>3. TypeOK  BY <1>2 DEF TypeOK
  <1>4. MsgInv  BY <1>2 DEF MsgInv
  <1>5. QED  BY <1>3, <1>4 DEF Inv

(* TypeOK gives properties of messages by type *)
LEMMA TypeOK_1b ==
  ASSUME TypeOK, NEW m \in sent, m.type = "1b"
  PROVE  /\ m.bal \in Ballots
         /\ m.maxVBal \in Ballots \cup {-1}
         /\ m.maxVal \in Values \cup {None}
         /\ m.acc \in Acceptors
  BY DEF TypeOK, Messages

LEMMA TypeOK_2a ==
  ASSUME TypeOK, NEW m \in sent, m.type = "2a"
  PROVE  /\ m.bal \in Ballots
         /\ m.val \in Values
  BY DEF TypeOK, Messages

LEMMA TypeOK_2b ==
  ASSUME TypeOK, NEW m \in sent, m.type = "2b"
  PROVE  /\ m.bal \in Ballots
         /\ m.val \in Values
         /\ m.acc \in Acceptors
  BY DEF TypeOK, Messages

(* Useful lemma: VotedForIn implies a 2b in sent and a 2a in sent with matching bal/val *)
LEMMA VotedInvImpliesVal ==
  ASSUME Inv, NEW a, NEW v, NEW b, VotedForIn(a, v, b)
  PROVE  \E m \in sent : m.type = "2a" /\ m.bal = b /\ m.val = v
  <1>1. PICK m2b \in sent : m2b.type = "2b" /\ m2b.val = v /\ m2b.bal = b /\ m2b.acc = a
    BY DEF VotedForIn
  <1>2. MsgInv2b(m2b)  BY <1>1, Inv DEF Inv, MsgInv
  <1>3. PICK m2a \in sent : m2a.type = "2a" /\ m2a.bal = m2b.bal /\ m2a.val = m2b.val
    BY <1>2 DEF MsgInv2b
  <1>4. QED  BY <1>1, <1>3

(* Two acceptors voting for v1 and v2 at the same ballot implies v1 = v2 *)
LEMMA OneValPerBallot ==
  ASSUME Inv, NEW a1, NEW a2, NEW v1, NEW v2, NEW b,
         VotedForIn(a1, v1, b), VotedForIn(a2, v2, b)
  PROVE  v1 = v2
  <1>1. \E m \in sent : m.type = "2a" /\ m.bal = b /\ m.val = v1
    BY VotedInvImpliesVal, Inv
  <1>2. \E m \in sent : m.type = "2a" /\ m.bal = b /\ m.val = v2
    BY VotedInvImpliesVal, Inv
  <1>3. PICK m_v1 \in sent : m_v1.type = "2a" /\ m_v1.bal = b /\ m_v1.val = v1
    BY <1>1
  <1>4. PICK m_v2 \in sent : m_v2.type = "2a" /\ m_v2.bal = b /\ m_v2.val = v2
    BY <1>2
  <1>5. MsgInv2a(m_v1)  BY <1>3, Inv DEF Inv, MsgInv
  <1>6. m_v2.val = m_v1.val  BY <1>5, <1>3, <1>4 DEF MsgInv2a
  <1>7. QED  BY <1>3, <1>4, <1>6

-----------------------------------------------------------------------------

(* The main inductive step *)
LEMMA NextImpliesInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Ballots

  \* Case 1: Stuttering - vars unchanged
  <1>U. CASE vars' = vars
    <2>1. sent' = sent  BY <1>U DEF vars
    <2>2. TypeOK'  BY <2>1, Inv DEF Inv, TypeOK
    <2>3. \A m, a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b)
      BY <2>1 DEF VotedForIn
    <2>4. \A a, b : DidNotVoteIn(a, b)' <=> DidNotVoteIn(a, b)
      BY <2>3 DEF DidNotVoteIn
    <2>5. \A a, b : WontVoteIn(a, b)' <=> WontVoteIn(a, b)
      BY <2>1, <2>4 DEF WontVoteIn
    <2>6. \A v, b : SafeAt(v, b)' <=> SafeAt(v, b)
      BY <2>3, <2>5 DEF SafeAt
    <2>7. \A m \in sent' :
            /\ (m.type = "1b") => MsgInv1b(m)'
            /\ (m.type = "2a") => MsgInv2a(m)'
            /\ (m.type = "2b") => MsgInv2b(m)'
      <3>1. SUFFICES ASSUME NEW m \in sent'
                     PROVE /\ (m.type = "1b") => MsgInv1b(m)'
                           /\ (m.type = "2a") => MsgInv2a(m)'
                           /\ (m.type = "2b") => MsgInv2b(m)'
        OBVIOUS
      <3>2. m \in sent  BY <2>1
      <3>3. /\ (m.type = "1b") => MsgInv1b(m)
            /\ (m.type = "2a") => MsgInv2a(m)
            /\ (m.type = "2b") => MsgInv2b(m)
        BY <3>2, Inv DEF Inv, MsgInv
      <3>4. (m.type = "1b") => MsgInv1b(m)'
        BY <3>3, <2>3, <2>4, <2>1 DEF MsgInv1b
      <3>5. (m.type = "2a") => MsgInv2a(m)'
        BY <3>3, <2>1, <2>6 DEF MsgInv2a
      <3>6. (m.type = "2b") => MsgInv2b(m)'
        BY <3>3, <2>1 DEF MsgInv2b
      <3>7. QED  BY <3>4, <3>5, <3>6
    <2>8. MsgInv'  BY <2>7 DEF MsgInv
    <2>9. QED  BY <2>2, <2>8 DEF Inv

  \* Case 2: Phase1a
  <1>1a. ASSUME NEW bb \in Ballots, Phase1a(bb) PROVE Inv'
    <2> DEFINE new == [type |-> "1a", bal |-> bb]
    <2>1. sent' = sent \cup {new}  BY <1>1a DEF Phase1a, Send
    <2>2. new \in Messages  BY DEF Messages
    <2>3. TypeOK'  BY <2>1, <2>2, Inv DEF Inv, TypeOK
    \* New message is not 2b, so VotedForIn doesn't change
    <2>4. \A a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b)
      BY <2>1 DEF VotedForIn
    <2>5. \A a, b : DidNotVoteIn(a, b)' <=> DidNotVoteIn(a, b)
      BY <2>4 DEF DidNotVoteIn
    <2>6. \A a, b : WontVoteIn(a, b) => WontVoteIn(a, b)'
      <3>1. SUFFICES ASSUME NEW a, NEW b, WontVoteIn(a, b)
                     PROVE WontVoteIn(a, b)'
        OBVIOUS
      <3>2. DidNotVoteIn(a, b)'  BY <3>1, <2>5 DEF WontVoteIn
      <3>3. \E mm \in sent : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > b
        BY <3>1 DEF WontVoteIn
      <3>4. \E mm \in sent' : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > b
        BY <3>3, <2>1
      <3>5. QED  BY <3>2, <3>4 DEF WontVoteIn
    <2>7. \A v, b : SafeAt(v, b) => SafeAt(v, b)'
      <3>1. SUFFICES ASSUME NEW v, NEW b, SafeAt(v, b), NEW c \in 0..(b-1)
                     PROVE \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
        BY DEF SafeAt
      <3>2. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
        BY <3>1 DEF SafeAt
      <3>3. \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
        BY <3>2, <2>4, <2>6
      <3>4. QED  BY <3>3
    <2>8. \A m \in sent' :
            /\ (m.type = "1b") => MsgInv1b(m)'
            /\ (m.type = "2a") => MsgInv2a(m)'
            /\ (m.type = "2b") => MsgInv2b(m)'
      <3>1. SUFFICES ASSUME NEW m \in sent'
                     PROVE /\ (m.type = "1b") => MsgInv1b(m)'
                           /\ (m.type = "2a") => MsgInv2a(m)'
                           /\ (m.type = "2b") => MsgInv2b(m)'
        OBVIOUS
      <3>2. CASE m = new
        <4>1. m.type = "1a"  BY <3>2
        <4>2. QED  BY <4>1
      <3>3. CASE m \in sent
        <4>1. /\ (m.type = "1b") => MsgInv1b(m)
              /\ (m.type = "2a") => MsgInv2a(m)
              /\ (m.type = "2b") => MsgInv2b(m)
          BY <3>3, Inv DEF Inv, MsgInv
        <4>2. (m.type = "1b") => MsgInv1b(m)'
          BY <4>1, <2>4, <2>5 DEF MsgInv1b
        <4>3. (m.type = "2a") => MsgInv2a(m)'
          <5>1. SUFFICES ASSUME m.type = "2a"
                         PROVE MsgInv2a(m)'
            OBVIOUS
          <5>2. MsgInv2a(m)  BY <4>1, <5>1
          <5>3. SafeAt(m.val, m.bal)  BY <5>2 DEF MsgInv2a
          <5>4. SafeAt(m.val, m.bal)'  BY <5>3, <2>7
          <5>5. \A m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal => m2.val = m.val
            BY <5>2 DEF MsgInv2a
          <5>6. \A m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal => m2.val = m.val
            <6>1. SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
                           PROVE m2.val = m.val
              OBVIOUS
            <6>2. CASE m2 = new
              <7>1. m2.type = "1a"  BY <6>2
              <7>2. QED  BY <7>1, <6>1
            <6>3. CASE m2 \in sent  BY <6>3, <5>5, <6>1
            <6>4. QED  BY <6>2, <6>3, <2>1
          <5>7. QED  BY <5>4, <5>6 DEF MsgInv2a
        <4>4. (m.type = "2b") => MsgInv2b(m)'
          <5>1. SUFFICES ASSUME m.type = "2b"
                         PROVE MsgInv2b(m)'
            OBVIOUS
          <5>2. MsgInv2b(m)  BY <4>1, <5>1
          <5>3. PICK m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
            BY <5>2 DEF MsgInv2b
          <5>4. m2 \in sent'  BY <5>3, <2>1
          <5>5. QED  BY <5>3, <5>4 DEF MsgInv2b
        <4>5. QED  BY <4>2, <4>3, <4>4
      <3>4. QED  BY <3>2, <3>3, <2>1
    <2>9. MsgInv'  BY <2>8 DEF MsgInv
    <2>10. QED  BY <2>3, <2>9 DEF Inv

  \* Case 3: Phase1b
  <1>1b. ASSUME NEW aa \in Acceptors, Phase1b(aa) PROVE Inv'
    <2>1. PICK m1a \in sent, r0 \in last_voted(aa) :
            /\ m1a.type = "1a"
            /\ \A m2 \in sent: m2.type \in {"1b","2b"} /\ m2.acc = aa => m1a.bal > m2.bal
            /\ sent' = sent \cup {[type |-> "1b", bal |-> m1a.bal,
                                    maxVBal |-> r0.bal, maxVal |-> r0.val, acc |-> aa]}
      BY <1>1b DEF Phase1b, Send
    <2> DEFINE new == [type |-> "1b", bal |-> m1a.bal,
                        maxVBal |-> r0.bal, maxVal |-> r0.val, acc |-> aa]
    <2> DEFINE TwoBs == {m \in sent : m.type = "2b" /\ m.acc = aa}
    <2>2. sent' = sent \cup {new}  BY <2>1
    <2>3. m1a.bal \in Ballots  BY <2>1, Inv DEF Inv, TypeOK, Messages

    <2>4. \/ (TwoBs = {} /\ r0 = [bal |-> -1, val |-> None])
          \/ (TwoBs # {} /\ r0 \in TwoBs /\ (\A m2 \in TwoBs : r0.bal >= m2.bal))
      <3>1. r0 \in last_voted(aa)  BY <2>1
      <3>2. last_voted(aa) = IF TwoBs # {}
                             THEN {m \in TwoBs : \A m2 \in TwoBs : m.bal >= m2.bal}
                             ELSE {[bal |-> -1, val |-> None]}
        BY DEF last_voted
      <3>3. CASE TwoBs = {}
        <4>1. last_voted(aa) = {[bal |-> -1, val |-> None]}  BY <3>2, <3>3
        <4>2. r0 = [bal |-> -1, val |-> None]  BY <4>1, <3>1
        <4>3. QED  BY <3>3, <4>2
      <3>4. CASE TwoBs # {}
        <4>1. last_voted(aa) = {m \in TwoBs : \A m2 \in TwoBs : m.bal >= m2.bal}
          BY <3>2, <3>4
        <4>2. r0 \in TwoBs /\ (\A m2 \in TwoBs : r0.bal >= m2.bal)
          BY <4>1, <3>1
        <4>3. QED  BY <3>4, <4>2
      <3>5. QED  BY <3>3, <3>4

    <2>5. r0.bal \in Ballots \cup {-1} /\ r0.val \in Values \cup {None}
      <3>1. CASE TwoBs = {} /\ r0 = [bal |-> -1, val |-> None]
        BY <3>1
      <3>2. CASE TwoBs # {} /\ r0 \in TwoBs /\ (\A m2 \in TwoBs : r0.bal >= m2.bal)
        <4>1. r0 \in sent /\ r0.type = "2b"  BY <3>2
        <4>1a. TypeOK  BY Inv DEF Inv
        <4>2. r0.bal \in Ballots /\ r0.val \in Values
          BY <4>1, <4>1a DEF TypeOK, Messages
        <4>3. QED  BY <4>2
      <3>3. QED  BY <2>4, <3>1, <3>2

    <2>6. new \in Messages  BY <2>3, <2>5, <1>1b DEF Messages
    <2>7. TypeOK'  BY <2>2, <2>6, Inv DEF Inv, TypeOK

    \* No new 2b, so VotedForIn unchanged
    <2>8. \A a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b)
      BY <2>2 DEF VotedForIn
    <2>9. \A a, b : DidNotVoteIn(a, b)' <=> DidNotVoteIn(a, b)
      BY <2>8 DEF DidNotVoteIn
    <2>10. \A a, b : WontVoteIn(a, b) => WontVoteIn(a, b)'
      <3>1. SUFFICES ASSUME NEW a, NEW b, WontVoteIn(a, b)
                     PROVE WontVoteIn(a, b)'
        OBVIOUS
      <3>2. DidNotVoteIn(a, b)'  BY <3>1, <2>9 DEF WontVoteIn
      <3>3. \E mm \in sent : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > b
        BY <3>1 DEF WontVoteIn
      <3>4. \E mm \in sent' : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > b
        BY <3>3, <2>2
      <3>5. QED  BY <3>2, <3>4 DEF WontVoteIn
    <2>11. \A v, b : SafeAt(v, b) => SafeAt(v, b)'
      <3>1. SUFFICES ASSUME NEW v, NEW b, SafeAt(v, b), NEW c \in 0..(b-1)
                     PROVE \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
        BY DEF SafeAt
      <3>2. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
        BY <3>1 DEF SafeAt
      <3>3. \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
        BY <3>2, <2>8, <2>10
      <3>4. QED  BY <3>3

    \* MsgInv1b for new message
    <2>12. MsgInv1b(new)'
      <3>1. SUFFICES /\ ((new.maxVBal >= 0) => /\ new.maxVal \in Values
                                                /\ VotedForIn(new.acc, new.maxVal, new.maxVBal)')
                     /\ \A bb \in (new.maxVBal+1)..(new.bal-1) : DidNotVoteIn(new.acc, bb)'
        BY DEF MsgInv1b
      <3>2. new.maxVBal = r0.bal /\ new.maxVal = r0.val /\ new.acc = aa /\ new.bal = m1a.bal
        OBVIOUS
      <3>3. (new.maxVBal >= 0) => /\ new.maxVal \in Values
                                  /\ VotedForIn(new.acc, new.maxVal, new.maxVBal)'
        <4>1. SUFFICES ASSUME new.maxVBal >= 0
                       PROVE /\ new.maxVal \in Values
                             /\ VotedForIn(new.acc, new.maxVal, new.maxVBal)'
          OBVIOUS
        <4>2. r0.bal >= 0  BY <4>1, <3>2
        <4>3. ~(r0 = [bal |-> -1, val |-> None])  BY <4>2
        <4>4. TwoBs # {} /\ r0 \in TwoBs /\ (\A m2 \in TwoBs : r0.bal >= m2.bal)
          BY <2>4, <4>3
        <4>5. r0 \in sent /\ r0.type = "2b" /\ r0.acc = aa  BY <4>4
        <4>5a. TypeOK  BY Inv DEF Inv
        <4>6. r0.val \in Values
          BY <4>5, <4>5a DEF TypeOK, Messages
        <4>7. new.maxVal \in Values  BY <4>6, <3>2
        <4>8. VotedForIn(aa, r0.val, r0.bal)  BY <4>5 DEF VotedForIn
        <4>9. VotedForIn(new.acc, new.maxVal, new.maxVBal)  BY <4>8, <3>2
        <4>10. VotedForIn(new.acc, new.maxVal, new.maxVBal)'  BY <4>9, <2>8
        <4>11. QED  BY <4>7, <4>10
      <3>4. \A b1 \in (new.maxVBal+1)..(new.bal-1) : DidNotVoteIn(new.acc, b1)'
        <4>1. SUFFICES ASSUME NEW b1 \in (new.maxVBal+1)..(new.bal-1)
                       PROVE DidNotVoteIn(new.acc, b1)
          BY <2>9
        <4>1a. new.maxVBal \in Int /\ new.bal \in Int
          BY <2>3, <2>5 DEF Ballots
        <4>2. b1 \in Int /\ b1 > new.maxVBal /\ b1 < new.bal
          BY <4>1, <4>1a
        <4>3. b1 > r0.bal  BY <4>2, <3>2
        <4>4. SUFFICES ASSUME NEW v \in Values
                       PROVE ~VotedForIn(aa, v, b1)
          BY <3>2 DEF DidNotVoteIn
        <4>5. SUFFICES ASSUME VotedForIn(aa, v, b1)
                       PROVE FALSE
          OBVIOUS
        <4>6. PICK m2b \in sent : m2b.type = "2b" /\ m2b.val = v /\ m2b.bal = b1 /\ m2b.acc = aa
          BY <4>5 DEF VotedForIn
        <4>7. m2b \in TwoBs  BY <4>6
        <4>8. CASE TwoBs = {}
          BY <4>7, <4>8
        <4>9. CASE TwoBs # {} /\ r0 \in TwoBs /\ (\A m2 \in TwoBs : r0.bal >= m2.bal)
          <5>0. TypeOK  BY Inv DEF Inv
          <5>0a. m2b.bal \in Int /\ r0.bal \in Int /\ b1 \in Int
            BY <4>6, <5>0, <4>2, <2>5 DEF TypeOK, Messages, Ballots
          <5>1. r0.bal >= m2b.bal  BY <4>9, <4>7
          <5>2. r0.bal >= b1  BY <5>1, <4>6, <5>0a
          <5>3. QED  BY <5>2, <4>3, <5>0a
        <4>10. QED  BY <2>4, <4>8, <4>9
      <3>5. QED  BY <3>3, <3>4

    \* MsgInv for all messages in sent'
    <2>13. \A m \in sent' :
             /\ (m.type = "1b") => MsgInv1b(m)'
             /\ (m.type = "2a") => MsgInv2a(m)'
             /\ (m.type = "2b") => MsgInv2b(m)'
      <3>1. SUFFICES ASSUME NEW m \in sent'
                     PROVE /\ (m.type = "1b") => MsgInv1b(m)'
                           /\ (m.type = "2a") => MsgInv2a(m)'
                           /\ (m.type = "2b") => MsgInv2b(m)'
        OBVIOUS
      <3>2. CASE m = new
        <4>1. m.type = "1b"  BY <3>2
        <4>2. MsgInv1b(m)'  BY <3>2, <2>12
        <4>3. ~(m.type = "2a") /\ ~(m.type = "2b")  BY <4>1
        <4>4. QED  BY <4>2, <4>3
      <3>3. CASE m \in sent
        <4>1. /\ (m.type = "1b") => MsgInv1b(m)
              /\ (m.type = "2a") => MsgInv2a(m)
              /\ (m.type = "2b") => MsgInv2b(m)
          BY <3>3, Inv DEF Inv, MsgInv
        <4>2. (m.type = "1b") => MsgInv1b(m)'
          BY <4>1, <2>8, <2>9 DEF MsgInv1b
        <4>3. (m.type = "2a") => MsgInv2a(m)'
          <5>1. SUFFICES ASSUME m.type = "2a"
                         PROVE MsgInv2a(m)'
            OBVIOUS
          <5>2. MsgInv2a(m)  BY <4>1, <5>1
          <5>3. SafeAt(m.val, m.bal)  BY <5>2 DEF MsgInv2a
          <5>4. SafeAt(m.val, m.bal)'  BY <5>3, <2>11
          <5>5. \A m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal => m2.val = m.val
            BY <5>2 DEF MsgInv2a
          <5>6. \A m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal => m2.val = m.val
            <6>1. SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
                           PROVE m2.val = m.val
              OBVIOUS
            <6>2. CASE m2 = new
              <7>1. m2.type = "1b"  BY <6>2
              <7>2. QED  BY <7>1, <6>1
            <6>3. CASE m2 \in sent  BY <6>3, <5>5, <6>1
            <6>4. QED  BY <6>2, <6>3, <2>2
          <5>7. QED  BY <5>4, <5>6 DEF MsgInv2a
        <4>4. (m.type = "2b") => MsgInv2b(m)'
          <5>1. SUFFICES ASSUME m.type = "2b"
                         PROVE MsgInv2b(m)'
            OBVIOUS
          <5>2. MsgInv2b(m)  BY <4>1, <5>1
          <5>3. PICK m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
            BY <5>2 DEF MsgInv2b
          <5>4. m2 \in sent'  BY <5>3, <2>2
          <5>5. QED  BY <5>3, <5>4 DEF MsgInv2b
        <4>5. QED  BY <4>2, <4>3, <4>4
      <3>4. QED  BY <3>2, <3>3, <2>2
    <2>14. MsgInv'  BY <2>13 DEF MsgInv
    <2>15. QED  BY <2>7, <2>14 DEF Inv

  \* Case 4: Phase2a
  <1>2a. ASSUME NEW bb \in Ballots, Phase2a(bb) PROVE Inv'
    <2>1. PICK v0 \in Values, Q0 \in Quorums,
                S0 \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = bb} :
            /\ \A a \in Q0 : \E m \in S0 : m.acc = a
            /\ \/ \A m \in S0 : m.maxVBal = -1
               \/ \E c \in 0..(bb-1) :
                    /\ \A m \in S0 : m.maxVBal =< c
                    /\ \E m \in S0 : /\ m.maxVBal = c
                                     /\ m.maxVal = v0
            /\ sent' = sent \cup {[type |-> "2a", bal |-> bb, val |-> v0]}
      BY <1>2a DEF Phase2a, Send
    <2> DEFINE new == [type |-> "2a", bal |-> bb, val |-> v0]
    <2>2. sent' = sent \cup {new}  BY <2>1
    <2>3. ~ \E m \in sent : m.type = "2a" /\ m.bal = bb
      BY <1>2a DEF Phase2a
    <2>4. new \in Messages  BY DEF Messages
    <2>5. TypeOK'  BY <2>2, <2>4, Inv DEF Inv, TypeOK

    \* No new 1b/2b, so VotedForIn, WontVoteIn, SafeAt unchanged
    <2>6. \A a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b)
      BY <2>2 DEF VotedForIn
    <2>7. \A a, b : DidNotVoteIn(a, b)' <=> DidNotVoteIn(a, b)
      BY <2>6 DEF DidNotVoteIn
    <2>8. \A a, b : WontVoteIn(a, b)' <=> WontVoteIn(a, b)
      <3>1. SUFFICES ASSUME NEW a, NEW b
                     PROVE WontVoteIn(a, b)' <=> WontVoteIn(a, b)
        OBVIOUS
      <3>2. (\E m \in sent' : m.type \in {"1b","2b"} /\ m.acc = a /\ m.bal > b)
            <=> (\E m \in sent : m.type \in {"1b","2b"} /\ m.acc = a /\ m.bal > b)
        BY <2>2
      <3>3. DidNotVoteIn(a, b)' <=> DidNotVoteIn(a, b)  BY <2>7
      <3>4. QED  BY <3>2, <3>3 DEF WontVoteIn
    <2>9. \A v, b : SafeAt(v, b)' <=> SafeAt(v, b)
      BY <2>6, <2>8 DEF SafeAt

    \* The main work: prove SafeAt(v0, bb)
    <2>10. SafeAt(v0, bb)
      <3>1. SUFFICES ASSUME NEW c \in 0..(bb-1)
                     PROVE \E Q \in Quorums : \A a \in Q : VotedForIn(a, v0, c) \/ WontVoteIn(a, c)
        BY DEF SafeAt
      <3>2. c \in Nat /\ c >= 0 /\ c < bb  BY <3>1
      <3>3. CASE \A m \in S0 : m.maxVBal = -1
        <4>1. WITNESS Q0 \in Quorums
        <4>2. SUFFICES ASSUME NEW a \in Q0
                       PROVE VotedForIn(a, v0, c) \/ WontVoteIn(a, c)
          OBVIOUS
        <4>3. PICK m \in S0 : m.acc = a  BY <2>1
        <4>4. m \in sent /\ m.type = "1b" /\ m.bal = bb /\ m.maxVBal = -1
          BY <4>3, <3>3, <2>1
        <4>5. MsgInv1b(m)  BY <4>4, Inv DEF Inv, MsgInv
        <4>6. \A b1 \in (m.maxVBal+1)..(m.bal-1) : DidNotVoteIn(m.acc, b1)
          BY <4>5 DEF MsgInv1b
        <4>7. (-1+1)..(bb-1) = 0..(bb-1)  OBVIOUS
        <4>8. c \in (m.maxVBal+1)..(m.bal-1)  BY <4>4, <3>2, <4>7
        <4>9. DidNotVoteIn(a, c)  BY <4>6, <4>3, <4>8
        <4>10. m.bal > c  BY <4>4, <3>2
        <4>11. \E mm \in sent : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > c
          BY <4>4, <4>3, <4>10
        <4>12. WontVoteIn(a, c)  BY <4>9, <4>11 DEF WontVoteIn
        <4>13. QED  BY <4>12
      <3>4. CASE \E c1 \in 0..(bb-1) :
                  (\A m \in S0 : m.maxVBal =< c1)
                  /\ (\E m \in S0 : m.maxVBal = c1 /\ m.maxVal = v0)
        <4>1. PICK c1 \in 0..(bb-1) :
                  (\A m \in S0 : m.maxVBal =< c1)
                  /\ (\E m \in S0 : m.maxVBal = c1 /\ m.maxVal = v0)
          BY <3>4
        <4>2. PICK mv \in S0 : mv.maxVBal = c1 /\ mv.maxVal = v0
          BY <4>1
        <4>3. c1 \in Nat /\ c1 >= 0 /\ c1 < bb  BY <4>1
        <4>4. mv \in sent /\ mv.type = "1b" /\ mv.bal = bb  BY <4>2, <2>1
        <4>5. MsgInv1b(mv)  BY <4>4, Inv DEF Inv, MsgInv
        <4>6. mv.maxVBal >= 0  BY <4>2, <4>3
        <4>7. v0 \in Values /\ VotedForIn(mv.acc, v0, c1)
          BY <4>5, <4>2, <4>6 DEF MsgInv1b
        <4>8. \E m_2a \in sent : m_2a.type = "2a" /\ m_2a.bal = c1 /\ m_2a.val = v0
          BY <4>7, VotedInvImpliesVal, Inv
        <4>9. PICK m_2a \in sent : m_2a.type = "2a" /\ m_2a.bal = c1 /\ m_2a.val = v0
          BY <4>8
        <4>10. MsgInv2a(m_2a)  BY <4>9, Inv DEF Inv, MsgInv
        <4>10a. SafeAt(m_2a.val, m_2a.bal)  BY <4>10 DEF MsgInv2a
        <4>11. SafeAt(v0, c1)  BY <4>10a, <4>9

        <4>12. CASE c < c1
          <5>1. c \in 0..(c1 - 1)  BY <4>12, <3>2, <4>3
          <5>2. \E Q \in Quorums : \A a \in Q : VotedForIn(a, v0, c) \/ WontVoteIn(a, c)
            BY <4>11, <5>1 DEF SafeAt
          <5>3. QED  BY <5>2

        <4>13. CASE c = c1
          <5>1. WITNESS Q0 \in Quorums
          <5>2. SUFFICES ASSUME NEW a \in Q0
                         PROVE VotedForIn(a, v0, c) \/ WontVoteIn(a, c)
            OBVIOUS
          <5>3. PICK m \in S0 : m.acc = a  BY <2>1
          <5>4. m \in sent /\ m.type = "1b" /\ m.bal = bb  BY <5>3, <2>1
          <5>5. m.maxVBal =< c1  BY <5>3, <4>1
          <5>6. m.maxVBal =< c  BY <5>5, <4>13
          <5>7. MsgInv1b(m)  BY <5>4, Inv DEF Inv, MsgInv
          <5>8. CASE m.maxVBal < c
            <6>1. c \in (m.maxVBal+1)..(m.bal-1)
              <7>0. TypeOK  BY Inv DEF Inv
              <7>1. m.maxVBal \in Int /\ m.bal \in Int
                BY <5>4, <7>0 DEF TypeOK, Messages, Ballots
              <7>2. c > m.maxVBal /\ c < m.bal  BY <5>8, <5>4, <3>2
              <7>3. QED  BY <7>1, <7>2, <3>2
            <6>2. DidNotVoteIn(a, c)  BY <5>7, <6>1, <5>3 DEF MsgInv1b
            <6>3. m.bal > c  BY <5>4, <3>2
            <6>4. \E mm \in sent : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > c
              BY <5>4, <5>3, <6>3
            <6>5. WontVoteIn(a, c)  BY <6>2, <6>4 DEF WontVoteIn
            <6>6. QED  BY <6>5
          <5>9. CASE m.maxVBal = c
            <6>1. m.maxVBal >= 0  BY <5>9, <4>13, <4>3
            <6>2. m.maxVal \in Values /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
              BY <5>7, <6>1 DEF MsgInv1b
            <6>3. m.maxVBal = c1  BY <5>9, <4>13
            <6>4. VotedForIn(m.acc, m.maxVal, c1)  BY <6>2, <6>3
            <6>5. \E m_2a_m \in sent : m_2a_m.type = "2a" /\ m_2a_m.bal = c1 /\ m_2a_m.val = m.maxVal
              BY <6>4, VotedInvImpliesVal, Inv, <6>2
            <6>6. PICK m_2a_m \in sent : m_2a_m.type = "2a" /\ m_2a_m.bal = c1 /\ m_2a_m.val = m.maxVal
              BY <6>5
            <6>7. m.maxVal = v0
              <7>1. \A m2 \in sent : m2.type = "2a" /\ m2.bal = m_2a.bal => m2.val = m_2a.val
                BY <4>10 DEF MsgInv2a
              <7>2. m_2a.bal = c1  BY <4>9
              <7>3. m_2a_m.bal = c1  BY <6>6
              <7>4. m_2a_m.val = m_2a.val  BY <7>1, <6>6, <7>2, <7>3
              <7>5. QED  BY <7>4, <4>9, <6>6
            <6>8. VotedForIn(a, v0, c)
              <7>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)  BY <6>2
              <7>2. m.acc = a  BY <5>3
              <7>3. m.maxVal = v0  BY <6>7
              <7>4. m.maxVBal = c  BY <5>9
              <7>5. QED  BY <7>1, <7>2, <7>3, <7>4
            <6>9. QED  BY <6>8
          <5>10. QED  BY <5>6, <5>8, <5>9

        <4>14. CASE c > c1
          <5>1. WITNESS Q0 \in Quorums
          <5>2. SUFFICES ASSUME NEW a \in Q0
                         PROVE VotedForIn(a, v0, c) \/ WontVoteIn(a, c)
            OBVIOUS
          <5>3. PICK m \in S0 : m.acc = a  BY <2>1
          <5>4. m \in sent /\ m.type = "1b" /\ m.bal = bb  BY <5>3, <2>1
          <5>4a. TypeOK  BY Inv DEF Inv
          <5>4b. m.maxVBal \in Int /\ m.bal \in Int
            BY <5>4, <5>4a DEF TypeOK, Messages, Ballots
          <5>5. m.maxVBal =< c1  BY <5>3, <4>1
          <5>6. m.maxVBal < c  BY <5>5, <4>14, <5>4b, <4>3, <3>2
          <5>7. MsgInv1b(m)  BY <5>4, Inv DEF Inv, MsgInv
          <5>9. c \in (m.maxVBal+1)..(m.bal-1)
            BY <5>6, <5>4, <3>2, <5>4b
          <5>10. DidNotVoteIn(a, c)  BY <5>7, <5>9, <5>3 DEF MsgInv1b
          <5>11. m.bal > c  BY <5>4, <3>2
          <5>12. \E mm \in sent : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > c
            BY <5>4, <5>3, <5>11
          <5>13. WontVoteIn(a, c)  BY <5>10, <5>12 DEF WontVoteIn
          <5>14. QED  BY <5>13

        <4>15. QED  BY <4>12, <4>13, <4>14, <3>2, <4>3
      <3>5. QED  BY <2>1, <3>3, <3>4

    \* MsgInv2a for new message
    <2>11. MsgInv2a(new)'
      <3>1. SafeAt(v0, bb)  BY <2>10
      <3>2. SafeAt(v0, bb)'  BY <3>1, <2>9
      <3>3. SafeAt(new.val, new.bal)'  BY <3>2
      <3>4. \A m2 \in sent' : m2.type = "2a" /\ m2.bal = new.bal => m2.val = new.val
        <4>1. SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = new.bal
                       PROVE m2.val = new.val
          OBVIOUS
        <4>2. CASE m2 \in sent
          <5>1. m2.bal = bb  BY <4>1
          <5>2. ~(m2.type = "2a" /\ m2.bal = bb)  BY <2>3, <4>2
          <5>3. QED  BY <5>2, <4>1, <5>1
        <4>3. CASE m2 = new  BY <4>3
        <4>4. QED  BY <4>2, <4>3, <2>2
      <3>5. QED  BY <3>3, <3>4 DEF MsgInv2a

    <2>12. \A m \in sent' :
             /\ (m.type = "1b") => MsgInv1b(m)'
             /\ (m.type = "2a") => MsgInv2a(m)'
             /\ (m.type = "2b") => MsgInv2b(m)'
      <3>1. SUFFICES ASSUME NEW m \in sent'
                     PROVE /\ (m.type = "1b") => MsgInv1b(m)'
                           /\ (m.type = "2a") => MsgInv2a(m)'
                           /\ (m.type = "2b") => MsgInv2b(m)'
        OBVIOUS
      <3>2. CASE m = new
        <4>1. m.type = "2a"  BY <3>2
        <4>2. MsgInv2a(m)'  BY <3>2, <2>11
        <4>3. ~(m.type = "1b") /\ ~(m.type = "2b")  BY <4>1
        <4>4. QED  BY <4>2, <4>3
      <3>3. CASE m \in sent
        <4>1. /\ (m.type = "1b") => MsgInv1b(m)
              /\ (m.type = "2a") => MsgInv2a(m)
              /\ (m.type = "2b") => MsgInv2b(m)
          BY <3>3, Inv DEF Inv, MsgInv
        <4>2. (m.type = "1b") => MsgInv1b(m)'
          BY <4>1, <2>6, <2>7 DEF MsgInv1b
        <4>3. (m.type = "2a") => MsgInv2a(m)'
          <5>1. SUFFICES ASSUME m.type = "2a"
                         PROVE MsgInv2a(m)'
            OBVIOUS
          <5>2. MsgInv2a(m)  BY <4>1, <5>1
          <5>3. SafeAt(m.val, m.bal)  BY <5>2 DEF MsgInv2a
          <5>4. SafeAt(m.val, m.bal)'  BY <5>3, <2>9
          <5>5. \A m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal => m2.val = m.val
            BY <5>2 DEF MsgInv2a
          <5>6. \A m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal => m2.val = m.val
            <6>1. SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
                           PROVE m2.val = m.val
              OBVIOUS
            <6>2. CASE m2 = new
              <7>1. m2.bal = bb  BY <6>2
              <7>2. m.bal = bb  BY <6>1, <7>1
              <7>3. m \in sent /\ m.type = "2a" /\ m.bal = bb  BY <3>3, <5>1, <7>2
              <7>4. QED  BY <7>3, <2>3
            <6>3. CASE m2 \in sent  BY <6>3, <5>5, <6>1
            <6>4. QED  BY <6>2, <6>3, <2>2
          <5>7. QED  BY <5>4, <5>6 DEF MsgInv2a
        <4>4. (m.type = "2b") => MsgInv2b(m)'
          <5>1. SUFFICES ASSUME m.type = "2b"
                         PROVE MsgInv2b(m)'
            OBVIOUS
          <5>2. MsgInv2b(m)  BY <4>1, <5>1
          <5>3. PICK m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
            BY <5>2 DEF MsgInv2b
          <5>4. m2 \in sent'  BY <5>3, <2>2
          <5>5. QED  BY <5>3, <5>4 DEF MsgInv2b
        <4>5. QED  BY <4>2, <4>3, <4>4
      <3>4. QED  BY <3>2, <3>3, <2>2
    <2>13. MsgInv'  BY <2>12 DEF MsgInv
    <2>14. QED  BY <2>5, <2>13 DEF Inv

  \* Case 5: Phase2b
  <1>2b. ASSUME NEW aa \in Acceptors, Phase2b(aa) PROVE Inv'
    <2>1. PICK m2a \in sent :
            /\ m2a.type = "2a"
            /\ \A m2 \in sent: m2.type \in {"1b","2b"} /\ m2.acc = aa => m2a.bal >= m2.bal
            /\ sent' = sent \cup {[type |-> "2b", bal |-> m2a.bal, val |-> m2a.val, acc |-> aa]}
      BY <1>2b DEF Phase2b, Send
    <2> DEFINE new == [type |-> "2b", bal |-> m2a.bal, val |-> m2a.val, acc |-> aa]
    <2>2. sent' = sent \cup {new}  BY <2>1
    <2>2a. TypeOK  BY Inv DEF Inv
    <2>3. m2a.bal \in Ballots /\ m2a.val \in Values
      BY <2>1, <2>2a DEF TypeOK, Messages
    <2>4. new \in Messages  BY <2>3, <1>2b DEF Messages
    <2>5. TypeOK'  BY <2>2, <2>4, Inv DEF Inv, TypeOK

    \* VotedForIn changes only by gaining (aa, m2a.val, m2a.bal)
    <2>6. \A a, v, b : VotedForIn(a, v, b)' <=>
                       (VotedForIn(a, v, b) \/ (a = aa /\ v = m2a.val /\ b = m2a.bal))
      <3>1. SUFFICES ASSUME NEW a, NEW v, NEW b
                     PROVE VotedForIn(a, v, b)' <=>
                       (VotedForIn(a, v, b) \/ (a = aa /\ v = m2a.val /\ b = m2a.bal))
        OBVIOUS
      <3>2. VotedForIn(a, v, b)' <=> (\E m \in sent' : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a)
        BY DEF VotedForIn
      <3>2a. VotedForIn(a, v, b) <=> (\E m \in sent : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a)
        BY DEF VotedForIn
      <3>3. (\E m \in sent' : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a)
            <=> ((\E m \in sent : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a)
                \/ (a = aa /\ v = m2a.val /\ b = m2a.bal))
        BY <2>2
      <3>4. QED  BY <3>2, <3>2a, <3>3

    \* DidNotVoteIn changes only at (aa, m2a.bal)
    <2>7. \A a, b : DidNotVoteIn(a, b) /\ ~(a = aa /\ b = m2a.bal) => DidNotVoteIn(a, b)'
      <3>1. SUFFICES ASSUME NEW a, NEW b,
                            DidNotVoteIn(a, b), ~(a = aa /\ b = m2a.bal),
                            NEW v \in Values
                     PROVE ~VotedForIn(a, v, b)'
        BY DEF DidNotVoteIn
      <3>2. ~VotedForIn(a, v, b)  BY <3>1 DEF DidNotVoteIn
      <3>3. ~(a = aa /\ v = m2a.val /\ b = m2a.bal)  BY <3>1
      <3>4. QED  BY <3>2, <3>3, <2>6

    \* WontVoteIn for (a, b) with a != aa or b != m2a.bal is preserved
    <2>8. \A a, b : WontVoteIn(a, b) /\ ~(a = aa /\ b = m2a.bal) => WontVoteIn(a, b)'
      <3>1. SUFFICES ASSUME NEW a, NEW b,
                            WontVoteIn(a, b), ~(a = aa /\ b = m2a.bal)
                     PROVE WontVoteIn(a, b)'
        OBVIOUS
      <3>2. DidNotVoteIn(a, b)  BY <3>1 DEF WontVoteIn
      <3>3. DidNotVoteIn(a, b)'  BY <3>2, <3>1, <2>7
      <3>4. \E mm \in sent : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > b
        BY <3>1 DEF WontVoteIn
      <3>5. \E mm \in sent' : mm.type \in {"1b","2b"} /\ mm.acc = a /\ mm.bal > b
        BY <3>4, <2>2
      <3>6. QED  BY <3>3, <3>5 DEF WontVoteIn

    \* WontVoteIn(aa, m2a.bal) is FALSE before the action (by precondition)
    <2>9. ~WontVoteIn(aa, m2a.bal)
      <3>1. SUFFICES ASSUME WontVoteIn(aa, m2a.bal) PROVE FALSE
        OBVIOUS
      <3>2. \E mm \in sent : mm.type \in {"1b","2b"} /\ mm.acc = aa /\ mm.bal > m2a.bal
        BY <3>1 DEF WontVoteIn
      <3>3. PICK mm \in sent : mm.type \in {"1b","2b"} /\ mm.acc = aa /\ mm.bal > m2a.bal
        BY <3>2
      <3>4. m2a.bal >= mm.bal  BY <3>3, <2>1
      <3>4a. mm.bal \in Nat /\ m2a.bal \in Nat
        BY <3>3, <2>2a, <2>3 DEF TypeOK, Messages, Ballots
      <3>5. QED  BY <3>3, <3>4, <3>4a

    \* For (a, b) = (aa, m2a.bal): WontVoteIn was false, so VotedForIn(a, v_old, m2a.bal) must hold,
    \* which by MsgInv2a uniqueness gives v_old = m2a.val.
    \* This means in the post-state, VotedForIn'(aa, v_old, m2a.bal) is true (we just voted).

    <2>10. \A v, b : SafeAt(v, b) => SafeAt(v, b)'
      <3>1. SUFFICES ASSUME NEW v, NEW b, SafeAt(v, b), NEW c \in 0..(b-1)
                     PROVE \E Q \in Quorums :
                             \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
        BY DEF SafeAt
      <3>2. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
        BY <3>1 DEF SafeAt
      <3>3. WITNESS Q \in Quorums
      <3>4. SUFFICES ASSUME NEW a \in Q
                     PROVE VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
        OBVIOUS
      <3>5. VotedForIn(a, v, c) \/ WontVoteIn(a, c)  BY <3>2
      <3>6. CASE VotedForIn(a, v, c)
        <4>1. VotedForIn(a, v, c)'  BY <3>6, <2>6
        <4>2. QED  BY <4>1
      <3>7. CASE WontVoteIn(a, c)
        <4>1. CASE ~(a = aa /\ c = m2a.bal)
          <5>1. WontVoteIn(a, c)'  BY <3>7, <4>1, <2>8
          <5>2. QED  BY <5>1
        <4>2. CASE a = aa /\ c = m2a.bal
          <5>1. WontVoteIn(aa, m2a.bal)  BY <3>7, <4>2
          <5>2. QED  BY <5>1, <2>9
        <4>3. QED  BY <4>1, <4>2
      <3>8. QED  BY <3>5, <3>6, <3>7

    \* MsgInv2b for new message: m2a itself is the 2a witness
    <2>11. MsgInv2b(new)'
      <3>1. m2a \in sent'  BY <2>1, <2>2
      <3>2. m2a.type = "2a" /\ m2a.bal = new.bal /\ m2a.val = new.val
        BY <2>1
      <3>3. QED  BY <3>1, <3>2 DEF MsgInv2b

    \* MsgInv for all messages
    <2>12. \A m \in sent' :
             /\ (m.type = "1b") => MsgInv1b(m)'
             /\ (m.type = "2a") => MsgInv2a(m)'
             /\ (m.type = "2b") => MsgInv2b(m)'
      <3>1. SUFFICES ASSUME NEW m \in sent'
                     PROVE /\ (m.type = "1b") => MsgInv1b(m)'
                           /\ (m.type = "2a") => MsgInv2a(m)'
                           /\ (m.type = "2b") => MsgInv2b(m)'
        OBVIOUS
      <3>2. CASE m = new
        <4>1. m.type = "2b"  BY <3>2
        <4>2. MsgInv2b(m)'  BY <3>2, <2>11
        <4>3. ~(m.type = "1b") /\ ~(m.type = "2a")  BY <4>1
        <4>4. QED  BY <4>2, <4>3
      <3>3. CASE m \in sent
        <4>1. /\ (m.type = "1b") => MsgInv1b(m)
              /\ (m.type = "2a") => MsgInv2a(m)
              /\ (m.type = "2b") => MsgInv2b(m)
          BY <3>3, Inv DEF Inv, MsgInv
        <4>2. (m.type = "1b") => MsgInv1b(m)'
          <5>1. SUFFICES ASSUME m.type = "1b"
                         PROVE MsgInv1b(m)'
            OBVIOUS
          <5>2. MsgInv1b(m)  BY <4>1, <5>1
          <5>3. (m.maxVBal >= 0) => /\ m.maxVal \in Values
                                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            BY <5>2 DEF MsgInv1b
          <5>4. (m.maxVBal >= 0) => /\ m.maxVal \in Values
                                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
            BY <5>3, <2>6
          <5>5. \A b1 \in (m.maxVBal+1)..(m.bal-1) : DidNotVoteIn(m.acc, b1)
            BY <5>2 DEF MsgInv1b
          <5>6. \A b1 \in (m.maxVBal+1)..(m.bal-1) : DidNotVoteIn(m.acc, b1)'
            <6>1. SUFFICES ASSUME NEW b1 \in (m.maxVBal+1)..(m.bal-1)
                           PROVE DidNotVoteIn(m.acc, b1)'
              OBVIOUS
            <6>2. DidNotVoteIn(m.acc, b1)  BY <5>5, <6>1
            <6>3a. m \in sent  BY <3>3
            <6>3. m.bal \in Nat /\ m.maxVBal \in Int /\ m2a.bal \in Nat
              BY <6>3a, <5>1, <2>2a, <2>3 DEF TypeOK, Messages, Ballots
            <6>4. b1 < m.bal /\ b1 \in Int
              BY <6>1, <6>3
            <6>5. ~(m.acc = aa /\ b1 = m2a.bal)
              <7>1. CASE m.acc # aa  BY <7>1
              <7>2. CASE m.acc = aa
                <8>1. m \in sent /\ m.type = "1b" /\ m.acc = aa  BY <6>3a, <5>1, <7>2
                <8>2. m2a.bal >= m.bal  BY <8>1, <2>1
                <8>3. b1 < m2a.bal  BY <6>4, <8>2, <6>3
                <8>4. QED  BY <8>3
              <7>3. QED  BY <7>1, <7>2
            <6>6. QED  BY <6>2, <6>5, <2>7
          <5>7. QED  BY <5>4, <5>6 DEF MsgInv1b
        <4>3. (m.type = "2a") => MsgInv2a(m)'
          <5>1. SUFFICES ASSUME m.type = "2a"
                         PROVE MsgInv2a(m)'
            OBVIOUS
          <5>2. MsgInv2a(m)  BY <4>1, <5>1
          <5>3. SafeAt(m.val, m.bal)  BY <5>2 DEF MsgInv2a
          <5>4. SafeAt(m.val, m.bal)'  BY <5>3, <2>10
          <5>5. \A m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal => m2.val = m.val
            BY <5>2 DEF MsgInv2a
          <5>6. \A m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal => m2.val = m.val
            <6>1. SUFFICES ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
                           PROVE m2.val = m.val
              OBVIOUS
            <6>2. CASE m2 = new
              <7>1. m2.type = "2b"  BY <6>2
              <7>2. QED  BY <7>1, <6>1
            <6>3. CASE m2 \in sent  BY <6>3, <5>5, <6>1
            <6>4. QED  BY <6>2, <6>3, <2>2
          <5>7. QED  BY <5>4, <5>6 DEF MsgInv2a
        <4>4. (m.type = "2b") => MsgInv2b(m)'
          <5>1. SUFFICES ASSUME m.type = "2b"
                         PROVE MsgInv2b(m)'
            OBVIOUS
          <5>2. MsgInv2b(m)  BY <4>1, <5>1
          <5>3. PICK mm \in sent : mm.type = "2a" /\ mm.bal = m.bal /\ mm.val = m.val
            BY <5>2 DEF MsgInv2b
          <5>4. mm \in sent'  BY <5>3, <2>2
          <5>5. QED  BY <5>3, <5>4 DEF MsgInv2b
        <4>5. QED  BY <4>2, <4>3, <4>4
      <3>4. QED  BY <3>2, <3>3, <2>2
    <2>13. MsgInv'  BY <2>12 DEF MsgInv
    <2>14. QED  BY <2>5, <2>13 DEF Inv

  <1>X. QED
    BY <1>U, <1>1a, <1>1b, <1>2a, <1>2b DEF Next, vars

-----------------------------------------------------------------------------

(* Spec implies always Inv *)
LEMMA SpecImpliesInv == Spec => []Inv
  <1>1. Init => Inv  BY InitImpliesInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextImpliesInv
  <1>3. QED  BY <1>1, <1>2, PTL DEF Spec

(* Asymmetric consistency: same- or earlier-ballot chosen value matches later-ballot chosen value *)
LEMMA ChosenInLE ==
  ASSUME Inv,
         NEW v1 \in Values, NEW v2 \in Values,
         NEW b1 \in Nat, NEW b2 \in Nat,
         ChosenIn(v1, b1), ChosenIn(v2, b2),
         b1 <= b2
  PROVE  v1 = v2
  <1>1. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
    BY DEF ChosenIn
  <1>2. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
    BY DEF ChosenIn
  <1>3. Q2 \cap Q2 # {}  BY QuorumAssumption
  <1>4. PICK a2 \in Q2 : TRUE  BY <1>3
  <1>5. VotedForIn(a2, v2, b2)  BY <1>1, <1>4

  <1>6. CASE b1 = b2
    <2>1. Q1 \cap Q2 # {}  BY QuorumAssumption
    <2>2. PICK a \in Q1 \cap Q2 : TRUE  BY <2>1
    <2>3. VotedForIn(a, v1, b1) /\ VotedForIn(a, v2, b2)
      BY <2>2, <1>1, <1>2
    <2>4. VotedForIn(a, v2, b1)  BY <2>3, <1>6
    <2>5. QED  BY OneValPerBallot, Inv, <2>3, <2>4

  <1>7. CASE b1 < b2
    <2>1. \E m \in sent : m.type = "2a" /\ m.bal = b2 /\ m.val = v2
      BY VotedInvImpliesVal, Inv, <1>5
    <2>2. PICK m \in sent : m.type = "2a" /\ m.bal = b2 /\ m.val = v2  BY <2>1
    <2>3. MsgInv2a(m)  BY <2>2, Inv DEF Inv, MsgInv
    <2>4. SafeAt(v2, b2)  BY <2>3, <2>2 DEF MsgInv2a
    <2>5. b1 \in 0..(b2-1)  BY <1>7
    <2>6. PICK Qsa \in Quorums : \A a \in Qsa : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
      BY <2>4, <2>5 DEF SafeAt
    <2>7. Q1 \cap Qsa # {}  BY QuorumAssumption
    <2>8. PICK a \in Q1 \cap Qsa : TRUE  BY <2>7
    <2>9. VotedForIn(a, v1, b1)  BY <2>8, <1>2
    <2>10. VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)  BY <2>8, <2>6
    <2>11. ~WontVoteIn(a, b1)
      <3>1. SUFFICES ASSUME WontVoteIn(a, b1) PROVE FALSE
        OBVIOUS
      <3>2. DidNotVoteIn(a, b1)  BY <3>1 DEF WontVoteIn
      <3>3. ~VotedForIn(a, v1, b1)  BY <3>2 DEF DidNotVoteIn
      <3>4. QED  BY <3>3, <2>9
    <2>12. VotedForIn(a, v2, b1)  BY <2>10, <2>11
    <2>13. QED  BY OneValPerBallot, Inv, <2>9, <2>12

  <1>8. QED  BY <1>6, <1>7

(* Inv implies Consistency *)
LEMMA InvImpliesConsistency ==
  ASSUME Inv, NEW v1 \in Values, NEW v2 \in Values, Chosen(v1), Chosen(v2)
  PROVE  v1 = v2
  <1>1. PICK b1 \in Ballots : ChosenIn(v1, b1)  BY DEF Chosen
  <1>2. PICK b2 \in Ballots : ChosenIn(v2, b2)  BY DEF Chosen
  <1>3. b1 \in Nat /\ b2 \in Nat  BY <1>1, <1>2 DEF Ballots
  <1>4. CASE b1 <= b2
    BY ChosenInLE, <1>4, Inv, <1>1, <1>2, <1>3
  <1>5. CASE b2 <= b1
    <2>1. v2 = v1  BY ChosenInLE, <1>5, Inv, <1>1, <1>2, <1>3
    <2>2. QED  BY <2>1
  <1>6. QED  BY <1>3, <1>4, <1>5

-----------------------------------------------------------------------------

THEOREM Consistent == Spec => []Consistency
  <1>1. Spec => []Inv  BY SpecImpliesInv
  <1>2. Inv => Consistency
    <2>1. SUFFICES ASSUME Inv,
                          NEW v1 \in Values, NEW v2 \in Values,
                          Chosen(v1), Chosen(v2)
                   PROVE v1 = v2
      BY DEF Consistency
    <2>2. QED  BY <2>1, InvImpliesConsistency
  <1>3. QED  BY <1>1, <1>2, PTL

=============================================================================

