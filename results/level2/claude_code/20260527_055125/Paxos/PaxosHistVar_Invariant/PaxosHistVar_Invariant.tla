------------------------------- MODULE PaxosHistVar_Invariant --------------------------

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

-----------------------------------------------------------------------------

Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK == sent \in SUBSET Messages

WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ \E m \in sent: m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b

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

-----------------------------------------------------------------------------

LEMMA QA == /\ Quorums \subseteq SUBSET Acceptors
            /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
BY QuorumAssumption

LEMMA InitInv == Init => Inv
BY DEF Init, Inv, TypeOK, MsgInv

LEMMA Ballots_Nat == Ballots = Nat
BY DEF Ballots

LEMMA NoNew2b_VotedSame ==
  ASSUME NEW mn, sent' = sent \cup {mn}, mn.type # "2b"
  PROVE \A a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b)
BY DEF VotedForIn

LEMMA NoNew2b_WontVotePreserved ==
  ASSUME NEW mn, sent' = sent \cup {mn}, mn.type # "2b",
         NEW a, NEW b, WontVoteIn(a, b)
  PROVE WontVoteIn(a, b)'
<1>1. \A v \in Values : ~VotedForIn(a, v, b) BY DEF WontVoteIn
<1>2. \A v \in Values : ~VotedForIn(a, v, b)' BY <1>1, NoNew2b_VotedSame
<1>3. \E m \in sent: m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b BY DEF WontVoteIn
<1>4. \E m \in sent': m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b BY <1>3
<1> QED BY <1>2, <1>4 DEF WontVoteIn

LEMMA NoNew2b_SafeAtPreserved ==
  ASSUME NEW mn, sent' = sent \cup {mn}, mn.type # "2b",
         NEW v, NEW b, SafeAt(v, b)
  PROVE SafeAt(v, b)'
<1>1. SUFFICES ASSUME NEW b2 \in 0..(b-1)
               PROVE \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
  BY DEF SafeAt
<1>2. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
  BY DEF SafeAt
<1>3. ASSUME NEW a \in Q PROVE VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
  <2>1. VotedForIn(a, v, b2) \/ WontVoteIn(a, b2) BY <1>2
  <2>2. CASE VotedForIn(a, v, b2)
    <3>1. VotedForIn(a, v, b2)' BY <2>2, NoNew2b_VotedSame
    <3> QED BY <3>1
  <2>3. CASE WontVoteIn(a, b2)
    <3>1. WontVoteIn(a, b2)' BY <2>3, NoNew2b_WontVotePreserved
    <3> QED BY <3>1
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>3

LEMMA TypeOKInv == Inv => TypeOK BY DEF Inv

LEMMA MsgInvInv == Inv => MsgInv BY DEF Inv

\* --- Inductive step ---

LEMMA InvInd == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
<1> USE QA DEF Inv, TypeOK

<1>1. CASE UNCHANGED vars
  <2>1. sent' = sent BY <1>1 DEF vars
  <2>2. TypeOK' BY <2>1
  <2>3. \A a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b) BY <2>1 DEF VotedForIn
  <2>4. \A a, b : WontVoteIn(a, b)' <=> WontVoteIn(a, b) BY <2>1 DEF WontVoteIn, VotedForIn
  <2>5. \A v, b : SafeAt(v, b)' <=> SafeAt(v, b) BY <2>3, <2>4 DEF SafeAt
  <2>6. MsgInv'
    <3>1. SUFFICES ASSUME NEW m \in sent'
                   PROVE /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                                              /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
                         /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                                              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
                         /\ m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                                                /\ m2.bal  = m.bal
                                                                /\ m2.val  = m.val
      BY DEF MsgInv
    <3>2. m \in sent BY <3>1, <2>1
    <3>3. /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                              /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
          /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                              /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
          /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                               /\ m2.bal  = m.bal
                                               /\ m2.val  = m.val
      BY <3>2 DEF MsgInv
    <3>4. m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                           /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
      BY <3>3, <2>3
    <3>5. m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                           /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
      BY <3>3, <2>5, <2>1
    <3>6. m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                             /\ m2.bal  = m.bal
                                             /\ m2.val  = m.val
      BY <3>3, <2>1
    <3> QED BY <3>4, <3>5, <3>6
  <2> QED BY <2>2, <2>6

<1>2. CASE \E b \in Ballots : Phase1a(b)
  <2>1. PICK b1 \in Ballots : Phase1a(b1) BY <1>2
  <2> DEFINE mn == [type |-> "1a", bal |-> b1]
  <2>2. sent' = sent \cup {mn} BY <2>1 DEF Phase1a, Send
  <2>3. mn \in Messages BY <2>1 DEF Messages
  <2>4. mn.type = "1a" OBVIOUS
  <2>5. TypeOK' BY <2>2, <2>3
  <2>6. \A a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b)
    BY <2>2, <2>4, NoNew2b_VotedSame
  <2>7. MsgInv'
    <3>1. SUFFICES ASSUME NEW m \in sent'
                   PROVE /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                                              /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
                         /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                                              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
                         /\ m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                                                /\ m2.bal  = m.bal
                                                                /\ m2.val  = m.val
      BY DEF MsgInv
    <3>2. CASE m = mn
      <4>1. m.type = "1a" BY <3>2
      <4> QED BY <4>1
    <3>3. CASE m \in sent
      <4>1. /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                                /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
            /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                                /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
            /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                                 /\ m2.bal  = m.bal
                                                 /\ m2.val  = m.val
        BY <3>3 DEF MsgInv
      <4>2. m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                             /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
        BY <4>1, <2>6
      <4>3. m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                             /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        <5>1. ASSUME m.type = "2a" PROVE SafeAt(m.val, m.bal)'
          <6>1. SafeAt(m.val, m.bal) BY <4>1, <5>1
          <6> QED BY <6>1, <2>2, <2>4, NoNew2b_SafeAtPreserved
        <5>2. ASSUME m.type = "2a", NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
              PROVE m2 = m
          <6>1. m2 # mn BY <5>2, <2>4
          <6>2. m2 \in sent BY <6>1, <5>2, <2>2
          <6>3. \A mz \in sent : (mz.type = "2a" /\ mz.bal = m.bal) => mz = m
            BY <3>3, <5>2 DEF MsgInv
          <6>4. m2.type = "2a" /\ m2.bal = m.bal BY <5>2
          <6> QED BY <6>2, <6>3, <6>4
        <5> QED BY <5>1, <5>2
      <4>4. m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                               /\ m2.bal  = m.bal
                                               /\ m2.val  = m.val
        BY <4>1, <2>2
      <4> QED BY <4>2, <4>3, <4>4
    <3> QED BY <3>1, <3>2, <3>3, <2>2
  <2> QED BY <2>5, <2>7

<1>3. CASE \E b \in Ballots : Phase2a(b)
  <2>1. PICK b1 \in Ballots : Phase2a(b1) BY <1>3
  <2>2. ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b1)
    BY <2>1 DEF Phase2a
  <2>3. PICK v1 \in Values, Q1 \in Quorums, S1 \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = b1} :
        /\ \A a \in Q1 : \E m \in S1 : m.acc = a
        /\ \/ \A m \in S1 : m.maxVBal = -1
           \/ \E c \in 0..(b1-1) :
                /\ \A m \in S1 : m.maxVBal =< c
                /\ \E m \in S1 : /\ m.maxVBal = c
                                 /\ m.maxVal = v1
        /\ Send([type |-> "2a", bal |-> b1, val |-> v1])
    BY <2>1 DEF Phase2a
  <2> DEFINE mn == [type |-> "2a", bal |-> b1, val |-> v1]
  <2>4. sent' = sent \cup {mn} BY <2>3 DEF Send
  <2>5. mn \in Messages BY <2>1 DEF Messages
  <2>6. mn.type = "2a" /\ mn.bal = b1 /\ mn.val = v1 OBVIOUS
  <2>7. TypeOK' BY <2>4, <2>5
  <2>8. \A a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b)
    BY <2>4, <2>6, NoNew2b_VotedSame
  <2>9. \A a, b : WontVoteIn(a, b) => WontVoteIn(a, b)'
    BY <2>4, <2>6, NoNew2b_WontVotePreserved
  <2>10. \A v, b : SafeAt(v, b) => SafeAt(v, b)'
    BY <2>4, <2>6, NoNew2b_SafeAtPreserved
  <2>11. S1 \subseteq sent
    BY <2>3
  <2>12. \A m \in S1 : m \in sent /\ m.type = "1b" /\ m.bal = b1
    BY <2>11, <2>3
  <2>13. \A m \in S1 : /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                      /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
    BY <2>12 DEF MsgInv
  \* Prove SafeAt(v1, b1)
  <2>14. SafeAt(v1, b1)
    <3>1. SUFFICES ASSUME NEW b2 \in 0..(b1-1)
                   PROVE \E Q \in Quorums : \A a \in Q : VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
      BY DEF SafeAt
    <3>2. b2 \in Ballots BY DEF Ballots
    <3>3. CASE \A m \in S1 : m.maxVBal = -1
      <4>1. \E Q \in Quorums : \A a \in Q : VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
        <5>1. WITNESS Q1 \in Quorums
        <5>2. ASSUME NEW a \in Q1 PROVE VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
          <6>1. PICK m1b \in S1 : m1b.acc = a BY <2>3
          <6>2. m1b \in sent /\ m1b.type = "1b" /\ m1b.bal = b1 /\ m1b.maxVBal = -1
            BY <6>1, <2>12, <3>3
          <6>3. b2 \in m1b.maxVBal+1..m1b.bal-1
            BY <6>2, <3>1, b2 \in 0..(b1-1) DEF Ballots
          <6>4. ~ \E v \in Values: VotedForIn(m1b.acc, v, b2)
            BY <6>3, <2>13, <6>1
          <6>5. \A v \in Values : ~VotedForIn(a, v, b2)
            BY <6>4, <6>1
          <6>6. \E m \in sent: m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b2
            <7>1. m1b.type = "1b" /\ m1b.acc = a /\ m1b.bal = b1
              BY <6>2, <6>1
            <7>2. b1 > b2 BY <3>1 DEF Ballots
            <7> QED BY <6>2, <7>1, <7>2
          <6>7. WontVoteIn(a, b2) BY <6>5, <6>6 DEF WontVoteIn
          <6> QED BY <6>7
        <5> QED BY <5>2
      <4> QED BY <4>1
    <3>4. CASE \E c \in 0..(b1-1) :
                /\ \A m \in S1 : m.maxVBal =< c
                /\ \E m \in S1 : /\ m.maxVBal = c
                                 /\ m.maxVal = v1
      <4>1. PICK c \in 0..(b1-1) :
                /\ \A m \in S1 : m.maxVBal =< c
                /\ \E m \in S1 : /\ m.maxVBal = c
                                 /\ m.maxVal = v1
        BY <3>4
      <4>2. PICK m_c \in S1 : m_c.maxVBal = c /\ m_c.maxVal = v1
        BY <4>1
      <4>3. c \in Ballots BY DEF Ballots
      <4>4. VotedForIn(m_c.acc, v1, c)
        <5>1. m_c \in sent /\ m_c.type = "1b" /\ m_c.bal = b1 BY <4>2, <2>12
        <5>2. \/ VotedForIn(m_c.acc, m_c.maxVal, m_c.maxVBal)
              \/ m_c.maxVBal = -1
          BY <2>13, <4>2
        <5>3. m_c.maxVBal = c BY <4>2
        <5>4. c >= 0 BY <4>1, c \in 0..(b1-1) DEF Ballots
        <5>5. m_c.maxVBal # -1 BY <5>3, <5>4
        <5>6. VotedForIn(m_c.acc, m_c.maxVal, m_c.maxVBal) BY <5>2, <5>5
        <5>7. VotedForIn(m_c.acc, v1, c) BY <5>6, <4>2
        <5> QED BY <5>7
      <4>5. \E m_2a \in sent : m_2a.type = "2a" /\ m_2a.bal = c /\ m_2a.val = v1
        <5>1. \E m_2b \in sent : m_2b.type = "2b" /\ m_2b.val = v1 /\ m_2b.bal = c /\ m_2b.acc = m_c.acc
          BY <4>4 DEF VotedForIn
        <5>2. PICK m_2b \in sent : m_2b.type = "2b" /\ m_2b.val = v1 /\ m_2b.bal = c /\ m_2b.acc = m_c.acc
          BY <5>1
        <5>3. \E m_2a \in sent : /\ m_2a.type = "2a"
                                 /\ m_2a.bal = m_2b.bal
                                 /\ m_2a.val = m_2b.val
          BY <5>2 DEF MsgInv
        <5> QED BY <5>2, <5>3
      <4>6. PICK m_2a_c \in sent : m_2a_c.type = "2a" /\ m_2a_c.bal = c /\ m_2a_c.val = v1
        BY <4>5
      <4>7. SafeAt(v1, c)
        BY <4>6 DEF MsgInv
      \* Now SafeAt(v1, b1) by cases on b2
      <4>8. CASE b2 = c
        <5>1. WITNESS Q1 \in Quorums
        <5>2. ASSUME NEW a \in Q1 PROVE VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
          <6>1. PICK m_a \in S1 : m_a.acc = a BY <2>3
          <6>2. m_a \in sent /\ m_a.type = "1b" /\ m_a.bal = b1
            BY <6>1, <2>12
          <6>3. m_a.maxVBal =< c BY <6>1, <4>1
          <6>4. CASE m_a.maxVBal = c
            \* VotedForIn(a, m_a.maxVal, c), need m_a.maxVal = v1
            <7>1. VotedForIn(m_a.acc, m_a.maxVal, m_a.maxVBal) \/ m_a.maxVBal = -1
              BY <2>13, <6>1
            <7>2. c >= 0 BY <4>1 DEF Ballots
            <7>3. m_a.maxVBal # -1 BY <6>4, <7>2
            <7>4. VotedForIn(m_a.acc, m_a.maxVal, m_a.maxVBal) BY <7>1, <7>3
            <7>5. VotedForIn(a, m_a.maxVal, c) BY <7>4, <6>4, <6>1
            \* Now need m_a.maxVal = v1
            <7>6. \E m_2b_a \in sent : m_2b_a.type = "2b" /\ m_2b_a.val = m_a.maxVal /\ m_2b_a.bal = c /\ m_2b_a.acc = a
              BY <7>5 DEF VotedForIn
            <7>7. PICK m_2b_a \in sent : m_2b_a.type = "2b" /\ m_2b_a.val = m_a.maxVal /\ m_2b_a.bal = c /\ m_2b_a.acc = a
              BY <7>6
            <7>8. \E m_2a_a \in sent : /\ m_2a_a.type = "2a"
                                       /\ m_2a_a.bal = m_2b_a.bal
                                       /\ m_2a_a.val = m_2b_a.val
              BY <7>7 DEF MsgInv
            <7>9. PICK m_2a_a \in sent : m_2a_a.type = "2a" /\ m_2a_a.bal = c /\ m_2a_a.val = m_a.maxVal
              BY <7>8, <7>7
            <7>10. m_2a_c = m_2a_a
              <8>1. \A m3 \in sent : (m3.type = "2a" /\ m3.bal = m_2a_c.bal) => m3 = m_2a_c
                BY <4>6 DEF MsgInv
              <8>2. m_2a_a.bal = m_2a_c.bal BY <4>6, <7>9
              <8>3. m_2a_a.type = "2a" BY <7>9
              <8> QED BY <8>1, <8>2, <8>3, <7>9
            <7>11. m_a.maxVal = v1 BY <7>10, <4>6, <7>9
            <7>12. VotedForIn(a, v1, b2) BY <7>5, <7>11, <4>8
            <7> QED BY <7>12
          <6>5. CASE m_a.maxVBal < c
            <7>1. \A b \in m_a.maxVBal+1..m_a.bal-1: ~\E v \in Values: VotedForIn(m_a.acc, v, b)
              BY <2>13, <6>1
            <7>2. m_a.maxVBal \in Ballots \cup {-1}
              <8>1. m_a \in Messages BY <6>2
              <8>2. m_a.maxVBal \in Ballots \cup {-1} BY <8>1, <6>2 DEF Messages
              <8> QED BY <8>2
            <7>3. m_a.bal = b1 /\ b1 \in Ballots BY <6>2, <2>1
            <7>4. c \in 0..(b1-1) BY <4>1
            <7>5. b2 = c BY <4>8
            <7>6. b2 \in m_a.maxVBal+1..m_a.bal-1
              <8>1. b2 = c BY <4>8
              <8>2. m_a.maxVBal < c BY <6>5
              <8>3. m_a.maxVBal+1 =< c BY <8>2, <7>2 DEF Ballots
              <8>4. c =< b1 - 1 BY <7>4 DEF Ballots
              <8>5. c =< m_a.bal - 1 BY <8>4, <7>3
              <8> QED BY <8>1, <8>3, <8>5, <7>2, <7>3 DEF Ballots
            <7>7. ~\E v \in Values: VotedForIn(m_a.acc, v, b2)
              BY <7>1, <7>6
            <7>8. \A v \in Values : ~VotedForIn(a, v, b2)
              BY <7>7, <6>1
            <7>9. m_a.type \in {"1b", "2b"} /\ m_a.acc = a /\ m_a.bal > b2
              <8>1. m_a.type = "1b" BY <6>2
              <8>2. m_a.bal = b1 BY <6>2
              <8>3. b1 > b2 BY <3>1, b2 \in 0..(b1-1) DEF Ballots
              <8> QED BY <8>1, <6>1, <8>2, <8>3
            <7>10. \E m \in sent: m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b2
              BY <6>2, <7>9
            <7>11. WontVoteIn(a, b2) BY <7>8, <7>10 DEF WontVoteIn
            <7> QED BY <7>11
          <6>6. m_a.maxVBal \in Ballots \cup {-1}
            <7>1. m_a \in Messages BY <6>2
            <7> QED BY <7>1, <6>2 DEF Messages
          <6>7. m_a.maxVBal =< c BY <6>3
          <6>8. m_a.maxVBal = c \/ m_a.maxVBal < c
            <7>1. m_a.maxVBal \in Int BY <6>6 DEF Ballots
            <7>2. c \in Int BY <4>1 DEF Ballots
            <7> QED BY <6>7, <7>1, <7>2
          <6> QED BY <6>4, <6>5, <6>8
        <5> QED BY <5>2
      <4>9. CASE b2 < c
        \* Use SafeAt(v1, c) from <4>7
        <5>1. b2 \in 0..(c-1)
          <6>1. b2 \in Nat BY <3>2 DEF Ballots
          <6>2. b2 < c BY <4>9
          <6>3. c \in Nat BY <4>1 DEF Ballots
          <6> QED BY <6>1, <6>2, <6>3
        <5>2. \E Q \in Quorums : \A a \in Q : VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
          BY <5>1, <4>7 DEF SafeAt
        <5> QED BY <5>2
      <4>10. CASE c < b2
        <5>1. WITNESS Q1 \in Quorums
        <5>2. ASSUME NEW a \in Q1 PROVE VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
          <6>1. PICK m_a \in S1 : m_a.acc = a BY <2>3
          <6>2. m_a \in sent /\ m_a.type = "1b" /\ m_a.bal = b1
            BY <6>1, <2>12
          <6>3. m_a.maxVBal =< c BY <6>1, <4>1
          <6>4. m_a.maxVBal \in Ballots \cup {-1}
            <7>1. m_a \in Messages BY <6>2
            <7> QED BY <7>1, <6>2 DEF Messages
          <6>5. \A b \in m_a.maxVBal+1..m_a.bal-1: ~\E v \in Values: VotedForIn(m_a.acc, v, b)
            BY <2>13, <6>1
          <6>6. b2 \in m_a.maxVBal+1..m_a.bal-1
            <7>1. m_a.maxVBal =< c BY <6>3
            <7>2. c < b2 BY <4>10
            <7>3. m_a.maxVBal+1 =< b2
              <8>1. m_a.maxVBal \in Int BY <6>4 DEF Ballots
              <8>2. c \in Int BY <4>1 DEF Ballots
              <8>3. b2 \in Int BY <3>2 DEF Ballots
              <8> QED BY <7>1, <7>2, <8>1, <8>2, <8>3
            <7>4. b2 =< m_a.bal - 1
              <8>1. m_a.bal = b1 BY <6>2
              <8>2. b2 =< b1 - 1 BY <3>1 DEF Ballots
              <8> QED BY <8>1, <8>2
            <7>5. m_a.maxVBal \in Int /\ m_a.bal \in Int /\ b2 \in Int
              BY <6>4, <6>2, <3>2 DEF Ballots, Messages
            <7> QED BY <7>3, <7>4, <7>5
          <6>7. ~\E v \in Values: VotedForIn(m_a.acc, v, b2)
            BY <6>5, <6>6
          <6>8. \A v \in Values : ~VotedForIn(a, v, b2)
            BY <6>7, <6>1
          <6>9. m_a.type \in {"1b", "2b"} /\ m_a.acc = a /\ m_a.bal > b2
            <7>1. b1 > b2 BY <3>1 DEF Ballots
            <7> QED BY <6>2, <6>1, <7>1
          <6>10. \E m \in sent: m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b2
            BY <6>2, <6>9
          <6>11. WontVoteIn(a, b2) BY <6>8, <6>10 DEF WontVoteIn
          <6> QED BY <6>11
        <5> QED BY <5>2
      <4>11. b2 = c \/ b2 < c \/ c < b2
        <5>1. b2 \in Int BY <3>2 DEF Ballots
        <5>2. c \in Int BY <4>1 DEF Ballots
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>8, <4>9, <4>10, <4>11
    <3> QED BY <3>3, <3>4, <2>3
  <2>15. MsgInv'
    <3>1. SUFFICES ASSUME NEW m \in sent'
                   PROVE /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                                              /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
                         /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                                              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
                         /\ m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                                                /\ m2.bal  = m.bal
                                                                /\ m2.val  = m.val
      BY DEF MsgInv
    <3>2. CASE m = mn
      \* New 2a message: prove SafeAt and uniqueness
      <4>1. m.type = "2a" /\ m.bal = b1 /\ m.val = v1 BY <3>2
      <4>2. SafeAt(m.val, m.bal)'
        <5>1. SafeAt(v1, b1) BY <2>14
        <5>2. SafeAt(v1, b1)' BY <5>1, <2>10
        <5> QED BY <5>2, <4>1
      <4>3. ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal PROVE m2 = m
        <5>1. m.bal = b1 BY <4>1
        <5>2. m2.bal = b1 BY <5>1, <4>3
        <5>3. m2.type = "2a" BY <4>3
        <5>4. CASE m2 \in sent
          <6>1. \E mz \in sent : mz.type = "2a" /\ mz.bal = b1 BY <5>2, <5>3, <5>4
          <6> QED BY <6>1, <2>2
        <5>5. CASE m2 = mn
          <6> QED BY <5>5, <3>2
        <5> QED BY <5>4, <5>5, <2>4
      <4> QED BY <4>1, <4>2, <4>3
    <3>3. CASE m \in sent
      <4>1. /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                                /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
            /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                                /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
            /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                                 /\ m2.bal  = m.bal
                                                 /\ m2.val  = m.val
        BY <3>3 DEF MsgInv
      <4>2. m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                             /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
        BY <4>1, <2>8
      <4>3. m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                             /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        <5>1. ASSUME m.type = "2a" PROVE SafeAt(m.val, m.bal)'
          BY <5>1, <4>1, <2>10
        <5>2. ASSUME m.type = "2a", NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
              PROVE m2 = m
          <6>1. CASE m2 = mn
            \* m2 = mn means m2.bal = b1, m2.type = "2a"
            \* m2.bal = m.bal = b1, m.type = "2a", m \in sent
            \* Contradicts <2>2 (no old 2a at b1)
            <7>1. m.type = "2a" /\ m.bal = b1 BY <6>1, <5>2
            <7>2. FALSE BY <7>1, <3>3, <2>2
            <7> QED BY <7>2
          <6>2. CASE m2 \in sent
            BY <6>2, <4>1, <5>2, <5>1
          <6> QED BY <6>1, <6>2, <2>4
        <5> QED BY <5>1, <5>2
      <4>4. m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                               /\ m2.bal  = m.bal
                                               /\ m2.val  = m.val
        BY <4>1, <2>4
      <4> QED BY <4>2, <4>3, <4>4
    <3> QED BY <3>1, <3>2, <3>3, <2>4
  <2> QED BY <2>7, <2>15

<1>4. CASE \E a \in Acceptors : Phase1b(a)
  <2>1. PICK a1 \in Acceptors : Phase1b(a1) BY <1>4
  <2>2. PICK m_1a \in sent, r \in last_voted(a1) :
        /\ m_1a.type = "1a"
        /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a1 => m_1a.bal > m2.bal
        /\ Send([type |-> "1b", bal |-> m_1a.bal, maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a1])
    BY <2>1 DEF Phase1b
  <2> DEFINE mn == [type |-> "1b", bal |-> m_1a.bal, maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a1]
  <2>3. sent' = sent \cup {mn} BY <2>2 DEF Send
  <2>4. m_1a \in Messages BY <2>2
  <2>5. m_1a.bal \in Ballots BY <2>4, <2>2 DEF Messages
  <2> DEFINE TwoBs == {m \in sent : m.type = "2b" /\ m.acc = a1}
  <2>6. last_voted(a1) = IF TwoBs # {} THEN {m \in TwoBs: \A m2 \in TwoBs: m.bal >= m2.bal}
                                       ELSE {[bal |-> -1, val |-> None]}
    BY DEF last_voted
  <2>7. r.bal \in Ballots \cup {-1} /\ r.val \in Values \cup {None}
    <3>1. CASE TwoBs # {}
      <4>1. r \in TwoBs BY <2>2, <2>6, <3>1
      <4>2. r \in Messages BY <4>1
      <4>3. r.type = "2b" /\ r.bal \in Ballots /\ r.val \in Values /\ r.acc = a1
        BY <4>1, <4>2 DEF Messages
      <4> QED BY <4>3
    <3>2. CASE TwoBs = {}
      <4>1. r = [bal |-> -1, val |-> None] BY <2>2, <2>6, <3>2
      <4>2. r.bal = -1 /\ r.val = None BY <4>1
      <4> QED BY <4>2
    <3> QED BY <3>1, <3>2
  <2>8. mn \in Messages BY <2>5, <2>7, <2>1 DEF Messages
  <2>9. mn.type = "1b" /\ mn.bal = m_1a.bal /\ mn.maxVBal = r.bal /\ mn.maxVal = r.val /\ mn.acc = a1
    OBVIOUS
  <2>10. TypeOK' BY <2>3, <2>8
  <2>11. \A a, v, b : VotedForIn(a, v, b)' <=> VotedForIn(a, v, b)
    BY <2>3, <2>9, NoNew2b_VotedSame
  <2>12. \A a, b : WontVoteIn(a, b) => WontVoteIn(a, b)'
    BY <2>3, <2>9, NoNew2b_WontVotePreserved
  <2>13. \A v, b : SafeAt(v, b) => SafeAt(v, b)'
    BY <2>3, <2>9, NoNew2b_SafeAtPreserved
  \* Now prove MsgInv for new 1b message
  <2>14. /\ VotedForIn(mn.acc, mn.maxVal, mn.maxVBal) \/ mn.maxVBal = -1
         /\ \A b \in mn.maxVBal+1..mn.bal-1: ~\E v \in Values: VotedForIn(mn.acc, v, b)
    <3>1. CASE TwoBs # {}
      <4>1. r \in TwoBs /\ \A m2 \in TwoBs: r.bal >= m2.bal BY <2>2, <2>6, <3>1
      <4>2. r.type = "2b" /\ r.acc = a1 BY <4>1
      <4>3. r \in Messages BY <4>1
      <4>4. r.bal \in Ballots /\ r.val \in Values BY <4>3, <4>2 DEF Messages
      <4>5. VotedForIn(a1, r.val, r.bal) BY <4>1, <4>2 DEF VotedForIn
      <4>6. VotedForIn(mn.acc, mn.maxVal, mn.maxVBal) BY <4>5, <2>9
      <4>7. ASSUME NEW b \in mn.maxVBal+1..mn.bal-1, NEW v \in Values, VotedForIn(mn.acc, v, b)
            PROVE FALSE
        <5>1. \E m_2b \in sent : m_2b.type = "2b" /\ m_2b.val = v /\ m_2b.bal = b /\ m_2b.acc = mn.acc
          BY <4>7 DEF VotedForIn
        <5>2. PICK m_2b \in sent : m_2b.type = "2b" /\ m_2b.val = v /\ m_2b.bal = b /\ m_2b.acc = a1
          BY <5>1, <2>9
        <5>3. m_2b \in TwoBs BY <5>2
        <5>4. r.bal >= m_2b.bal BY <4>1, <5>3
        <5>5. b > r.bal
          <6>1. b \in mn.maxVBal+1..mn.bal-1 BY <4>7
          <6>2. mn.maxVBal = r.bal BY <2>9
          <6>3. b \in r.bal+1..mn.bal-1 BY <6>1, <6>2
          <6>4. r.bal \in Int BY <4>4 DEF Ballots
          <6>5. mn.bal \in Int BY <2>8 DEF Messages, Ballots
          <6>6. b \in Int /\ b > r.bal BY <6>3, <6>4, <6>5
          <6> QED BY <6>6
        <5>6. m_2b.bal = b BY <5>2
        <5>7. r.bal >= b BY <5>4, <5>6
        <5> QED BY <5>5, <5>7, <4>4 DEF Ballots
      <4>8. \A b \in mn.maxVBal+1..mn.bal-1: ~\E v \in Values: VotedForIn(mn.acc, v, b)
        BY <4>7
      <4> QED BY <4>6, <4>8
    <3>2. CASE TwoBs = {}
      <4>1. r = [bal |-> -1, val |-> None] BY <2>2, <2>6, <3>2
      <4>2. r.bal = -1 BY <4>1
      <4>3. mn.maxVBal = -1 BY <4>2, <2>9
      <4>4. ASSUME NEW b \in mn.maxVBal+1..mn.bal-1, NEW v \in Values, VotedForIn(mn.acc, v, b)
            PROVE FALSE
        <5>1. \E m_2b \in sent : m_2b.type = "2b" /\ m_2b.val = v /\ m_2b.bal = b /\ m_2b.acc = a1
          BY <4>4, <2>9 DEF VotedForIn
        <5>2. PICK m_2b \in sent : m_2b.type = "2b" /\ m_2b.acc = a1 BY <5>1
        <5>3. m_2b \in TwoBs BY <5>2
        <5> QED BY <5>3, <3>2
      <4>5. \A b \in mn.maxVBal+1..mn.bal-1: ~\E v \in Values: VotedForIn(mn.acc, v, b)
        BY <4>4
      <4> QED BY <4>3, <4>5
    <3> QED BY <3>1, <3>2
  <2>15. /\ VotedForIn(mn.acc, mn.maxVal, mn.maxVBal)' \/ mn.maxVBal = -1
         /\ \A b \in mn.maxVBal+1..mn.bal-1: ~\E v \in Values: VotedForIn(mn.acc, v, b)'
    BY <2>14, <2>11
  <2>16. MsgInv'
    <3>1. SUFFICES ASSUME NEW m \in sent'
                   PROVE /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                                              /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
                         /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                                              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
                         /\ m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                                                /\ m2.bal  = m.bal
                                                                /\ m2.val  = m.val
      BY DEF MsgInv
    <3>2. CASE m = mn
      <4>1. m.type = "1b" BY <3>2, <2>9
      <4>2. m.type # "2a" /\ m.type # "2b" BY <4>1
      <4>3. /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
            /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
        BY <3>2, <2>15
      <4> QED BY <4>1, <4>2, <4>3
    <3>3. CASE m \in sent
      <4>1. /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                                /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
            /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                                /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
            /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                                 /\ m2.bal  = m.bal
                                                 /\ m2.val  = m.val
        BY <3>3 DEF MsgInv
      <4>2. m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                             /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
        BY <4>1, <2>11
      <4>3. m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                             /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        <5>1. ASSUME m.type = "2a" PROVE SafeAt(m.val, m.bal)'
          BY <5>1, <4>1, <2>13
        <5>2. ASSUME m.type = "2a", NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal
              PROVE m2 = m
          <6>1. m2 # mn BY <5>2, <2>9
          <6>2. m2 \in sent BY <6>1, <5>2, <2>3
          <6>3. \A mz \in sent : (mz.type = "2a" /\ mz.bal = m.bal) => mz = m
            BY <3>3, <5>2 DEF MsgInv
          <6>4. m2.type = "2a" /\ m2.bal = m.bal BY <5>2
          <6> QED BY <6>2, <6>3, <6>4
        <5> QED BY <5>1, <5>2
      <4>4. m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                               /\ m2.bal  = m.bal
                                               /\ m2.val  = m.val
        BY <4>1, <2>3
      <4> QED BY <4>2, <4>3, <4>4
    <3> QED BY <3>1, <3>2, <3>3, <2>3
  <2> QED BY <2>10, <2>16

<1>5. CASE \E a \in Acceptors : Phase2b(a)
  <2>1. PICK a1 \in Acceptors : Phase2b(a1) BY <1>5
  <2>2. PICK m_2a \in sent :
        /\ m_2a.type = "2a"
        /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a1 => m_2a.bal >= m2.bal
        /\ Send([type |-> "2b", bal |-> m_2a.bal, val |-> m_2a.val, acc |-> a1])
    BY <2>1 DEF Phase2b
  <2> DEFINE mn == [type |-> "2b", bal |-> m_2a.bal, val |-> m_2a.val, acc |-> a1]
  <2>3. sent' = sent \cup {mn} BY <2>2 DEF Send
  <2>4. m_2a \in Messages BY <2>2
  <2>5. m_2a.bal \in Ballots /\ m_2a.val \in Values
    BY <2>4, <2>2 DEF Messages
  <2>6. mn \in Messages BY <2>5, <2>1 DEF Messages
  <2>7. mn.type = "2b" /\ mn.bal = m_2a.bal /\ mn.val = m_2a.val /\ mn.acc = a1
    OBVIOUS
  <2>8. TypeOK' BY <2>3, <2>6
  \* Phase2b adds a new 2b. We need careful analysis.
  <2>9. \A a, v, b : VotedForIn(a, v, b) => VotedForIn(a, v, b)'
    BY <2>3 DEF VotedForIn
  \* Critical: WontVoteIn is preserved
  <2>10. \A a, b : WontVoteIn(a, b) => WontVoteIn(a, b)'
    <3>1. SUFFICES ASSUME NEW a, NEW b, WontVoteIn(a, b)
                   PROVE WontVoteIn(a, b)'
      OBVIOUS
    <3>2. \A v \in Values : ~VotedForIn(a, v, b) BY <3>1 DEF WontVoteIn
    <3>3. \E m \in sent : m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b
      BY <3>1 DEF WontVoteIn
    <3>4. \A v \in Values : ~VotedForIn(a, v, b)'
      <4>1. SUFFICES ASSUME NEW v \in Values, VotedForIn(a, v, b)' PROVE FALSE
        OBVIOUS
      <4>2. \E m \in sent' : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a
        BY <4>1 DEF VotedForIn
      <4>3. PICK m_v \in sent' : m_v.type = "2b" /\ m_v.val = v /\ m_v.bal = b /\ m_v.acc = a
        BY <4>2
      <4>4. CASE m_v \in sent
        <5>1. VotedForIn(a, v, b) BY <4>4, <4>3 DEF VotedForIn
        <5> QED BY <5>1, <3>2
      <4>5. CASE m_v = mn
        <5>1. m_v.bal = m_2a.bal /\ m_v.acc = a1 BY <4>5, <2>7
        <5>2. PICK m_w \in sent : m_w.type \in {"1b", "2b"} /\ m_w.acc = a /\ m_w.bal > b
          BY <3>3
        <5>3. a = a1 BY <5>1, <4>3
        <5>4. m_w.acc = a1 BY <5>2, <5>3
        <5>5. m_2a.bal >= m_w.bal BY <2>2, <5>2, <5>4
        <5>5a. m_w \in Messages BY <5>2
        <5>5b. m_w.bal \in Nat BY <5>5a, <5>2 DEF Messages, Ballots
        <5>5c. b = m_v.bal BY <4>3
        <5>5d. b = m_2a.bal BY <5>1, <5>5c
        <5>5e. b \in Nat BY <5>5d, <2>5 DEF Ballots
        <5>6. m_w.bal > b BY <5>2
        <5>7. m_2a.bal > b BY <5>5, <5>5b, <5>5e, <5>6, <2>5 DEF Ballots
        <5>10. b > b BY <5>7, <5>5d
        <5> QED BY <5>10, <5>5e
      <4> QED BY <4>4, <4>5, <2>3, <4>3
    <3>5. \E m \in sent' : m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b
      BY <3>3, <2>3
    <3> QED BY <3>4, <3>5 DEF WontVoteIn
  <2>11. \A v, b : SafeAt(v, b) => SafeAt(v, b)'
    <3>1. SUFFICES ASSUME NEW v, NEW b, SafeAt(v, b)
                   PROVE SafeAt(v, b)'
      OBVIOUS
    <3>2. SUFFICES ASSUME NEW b2 \in 0..(b-1)
                   PROVE \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
      BY DEF SafeAt
    <3>3. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)
      BY <3>1 DEF SafeAt
    <3>4. ASSUME NEW a \in Q PROVE VotedForIn(a, v, b2)' \/ WontVoteIn(a, b2)'
      <4>1. VotedForIn(a, v, b2) \/ WontVoteIn(a, b2) BY <3>3
      <4>2. CASE VotedForIn(a, v, b2) BY <4>2, <2>9
      <4>3. CASE WontVoteIn(a, b2) BY <4>3, <2>10
      <4> QED BY <4>1, <4>2, <4>3
    <3> QED BY <3>4
  <2>12. MsgInv'
    <3>1. SUFFICES ASSUME NEW m \in sent'
                   PROVE /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                                              /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
                         /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)'
                                              /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
                         /\ m.type = "2b" => \E m2 \in sent' : /\ m2.type = "2a"
                                                                /\ m2.bal  = m.bal
                                                                /\ m2.val  = m.val
      BY DEF MsgInv
    <3>2. CASE m = mn
      <4>1. m.type = "2b" /\ m.bal = m_2a.bal /\ m.val = m_2a.val /\ m.acc = a1 BY <3>2
      <4>2. m.type # "1b" /\ m.type # "2a" BY <4>1
      <4>3. \E m2 \in sent' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
        <5>1. m_2a.type = "2a" BY <2>2
        <5>2. m_2a \in sent' BY <2>2, <2>3
        <5>3. m_2a.bal = m.bal /\ m_2a.val = m.val BY <4>1
        <5> QED BY <5>1, <5>2, <5>3
      <4> QED BY <4>1, <4>2, <4>3
    <3>3. CASE m \in sent
      <4>1. /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                                /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
            /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                                /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
            /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                                 /\ m2.bal  = m.bal
                                                 /\ m2.val  = m.val
        BY <3>3 DEF MsgInv
      <4>2. ASSUME m.type = "1b" PROVE /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
                                       /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
        <5>1. VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
          BY <4>1, <4>2
        <5>2. \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
          BY <4>1, <4>2
        <5>3. VotedForIn(m.acc, m.maxVal, m.maxVBal)' \/ m.maxVBal = -1
          BY <5>1, <2>9
        <5>4. ASSUME NEW b \in m.maxVBal+1..m.bal-1, NEW v \in Values, VotedForIn(m.acc, v, b)'
              PROVE FALSE
          <6>1. \E m_2b \in sent' : m_2b.type = "2b" /\ m_2b.val = v /\ m_2b.bal = b /\ m_2b.acc = m.acc
            BY <5>4 DEF VotedForIn
          <6>2. PICK m_2b \in sent' : m_2b.type = "2b" /\ m_2b.val = v /\ m_2b.bal = b /\ m_2b.acc = m.acc
            BY <6>1
          <6>3. CASE m_2b \in sent
            <7>1. VotedForIn(m.acc, v, b) BY <6>3, <6>2 DEF VotedForIn
            <7> QED BY <7>1, <5>2, <5>4
          <6>4. CASE m_2b = mn
            <7>1. m_2b.bal = m_2a.bal /\ m_2b.acc = a1 BY <6>4, <2>7
            <7>2. m.acc = a1 BY <7>1, <6>2
            <7>3. m.type \in {"1b", "2b"} /\ m.acc = a1 BY <4>2, <7>2
            <7>4. m_2a.bal >= m.bal BY <2>2, <3>3, <7>3
            <7>5. b = m_2a.bal BY <6>2, <7>1
            <7>6. b >= m.bal BY <7>5, <7>4
            <7>7. b \in m.maxVBal+1..m.bal-1 BY <5>4
            <7>8. b <= m.bal - 1
              <8>1. m.bal \in Int
                <9>1. m \in Messages BY <3>3
                <9> QED BY <9>1, <4>2 DEF Messages, Ballots
              <8>2. b \in Int BY <7>7, <8>1
              <8> QED BY <7>7, <8>1, <8>2
            <7>9. m.bal \in Int
              <8>1. m \in Messages BY <3>3
              <8> QED BY <8>1, <4>2 DEF Messages, Ballots
            <7> QED BY <7>6, <7>8, <7>9
          <6> QED BY <6>2, <6>3, <6>4, <2>3
        <5>5. \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)'
          BY <5>4
        <5> QED BY <5>3, <5>5
      <4>3. ASSUME m.type = "2a" PROVE /\ SafeAt(m.val, m.bal)'
                                       /\ \A m2 \in sent' : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
        <5>1. SafeAt(m.val, m.bal) BY <4>1, <4>3
        <5>2. SafeAt(m.val, m.bal)' BY <5>1, <2>11
        <5>3. ASSUME NEW m2 \in sent', m2.type = "2a", m2.bal = m.bal PROVE m2 = m
          <6>1. m2 # mn BY <5>3, <2>7
          <6>2. m2 \in sent BY <6>1, <5>3, <2>3
          <6>3. \A m3 \in sent : (m3.type = "2a" /\ m3.bal = m.bal) => m3 = m
            BY <4>1, <4>3
          <6> QED BY <6>2, <6>3, <5>3
        <5> QED BY <5>2, <5>3
      <4>4. ASSUME m.type = "2b" PROVE \E m2 \in sent' : /\ m2.type = "2a"
                                                         /\ m2.bal  = m.bal
                                                         /\ m2.val  = m.val
        <5>1. \E m2 \in sent : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
          BY <4>1, <4>4
        <5> QED BY <5>1, <2>3
      <4> QED BY <4>2, <4>3, <4>4
    <3> QED BY <3>1, <3>2, <3>3, <2>3
  <2> QED BY <2>8, <2>12

<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

-----------------------------------------------------------------------------

THEOREM Invariant == Spec => []Inv
<1>1. Init => Inv BY InitInv
<1>2. Inv /\ [Next]_vars => Inv' BY InvInd
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

=============================================================================

