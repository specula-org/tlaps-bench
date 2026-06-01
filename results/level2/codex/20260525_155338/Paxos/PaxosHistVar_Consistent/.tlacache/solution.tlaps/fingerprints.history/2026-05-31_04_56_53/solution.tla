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

-----------------------------------------------------------------------------

TypeOK ==
  \A m \in sent :
    \/ /\ m.type = "1a"
       /\ m.bal \in Ballots
    \/ /\ m.type = "1b"
       /\ m.bal \in Ballots
       /\ m.acc \in Acceptors
       /\ m.maxVBal \in {-1} \cup Ballots
       /\ m.maxVBal < m.bal
    \/ /\ m.type = "2a"
       /\ m.bal \in Ballots
       /\ m.val \in Values
    \/ /\ m.type = "2b"
       /\ m.bal \in Ballots
       /\ m.val \in Values
       /\ m.acc \in Acceptors

MsgInv ==
  /\ \A m \in sent : m.type = "1a" => m.bal \in Ballots
  /\ \A m \in sent : m.type = "1b" =>
        /\ m.bal \in Ballots
        /\ m.maxVBal \in {-1} \cup Ballots
  /\ \A m \in sent : m.type = "2a" =>
        /\ m.bal \in Ballots
        /\ m.val \in Values
  /\ \A m \in sent : m.type = "2b" =>
        /\ m.bal \in Ballots
        /\ m.val \in Values

Unique2a ==
  \A m, n \in sent :
    m.type = "2a" /\ n.type = "2a" /\ m.bal = n.bal => m.val = n.val

VoteInv ==
  \A m \in sent :
    m.type = "2b" =>
      \E n \in sent : /\ n.type = "2a"
                      /\ n.bal = m.bal
                      /\ n.val = m.val

PromiseInv ==
  \A m \in sent :
    m.type = "1b" =>
      /\ m.maxVBal = -1 \/ VotedForIn(m.acc, m.maxVal, m.maxVBal)
      /\ \A n \in sent :
           n.type = "2b" /\ n.acc = m.acc /\ n.bal < m.bal
             => n.bal <= m.maxVBal

ProposalInv ==
  \A p \in sent :
    p.type = "2a" =>
      \E Q \in Quorums, S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = p.bal}:
        /\ \A a \in Q : \E m \in S : m.acc = a
        /\ \/ \A m \in S : m.maxVBal = -1
           \/ \E c \in 0..(p.bal-1) :
                /\ \A m \in S : m.maxVBal =< c
                /\ \E m \in S : /\ m.maxVBal = c
                                /\ m.maxVal = p.val

IndInv == MsgInv /\ Unique2a /\ VoteInv /\ PromiseInv /\ ProposalInv

SafeAt(b, v) ==
  \A c \in 0..(b-1) : \A w \in Values : ChosenIn(w, c) => w = v

SafeAtBallot(b) ==
  \A p \in sent : p.type = "2a" /\ p.bal = b => SafeAt(b, p.val)

THEOREM LastVotedProps ==
  \A a, r :
    r \in last_voted(a) =>
      /\ r.bal = -1 \/ (r \in sent /\ r.type = "2b" /\ r.acc = a)
      /\ \A m \in sent : m.type = "2b" /\ m.acc = a => m.bal <= r.bal
PROOF
  BY SMT DEF last_voted

THEOREM VoteValueUnique ==
  IndInv =>
    \A a1, a2, v1, v2, b :
      VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => v1 = v2
PROOF
  BY SMT DEF IndInv, VoteInv, Unique2a, VotedForIn

THEOREM PromiseLower ==
  IndInv =>
    \A s, n \in sent :
      s.type = "1b" /\ n.type = "2b" /\ n.acc = s.acc /\ n.bal < s.bal
        => n.bal <= s.maxVBal
PROOF
  BY SMT DEF IndInv, PromiseInv

THEOREM LeqTrans ==
  \A x, y, z \in Int : x <= y /\ y <= z => x <= z
PROOF
  BY SimpleArithmetic

THEOREM ProposalInvAddNon2a ==
  ASSUME ProposalInv,
         NEW newMsg,
         sent' = sent \cup {newMsg},
         newMsg.type # "2a"
PROVE  ProposalInv'
PROOF
<1>1. ProposalInv
  OBVIOUS
<1>2. SUFFICES ASSUME NEW p \in sent',
                       p.type = "2a"
                PROVE  \E Q \in Quorums,
                          S \in SUBSET {m \in sent' : m.type = "1b" /\ m.bal = p.bal} :
                          /\ \A a \in Q : \E m \in S : m.acc = a
                          /\ \/ \A m \in S : m.maxVBal = -1
                             \/ \E c \in 0..(p.bal-1) :
                                  /\ \A m \in S : m.maxVBal =< c
                                  /\ \E m \in S : /\ m.maxVBal = c
                                                  /\ m.maxVal = p.val
  BY DEF ProposalInv
<1>3. ASSUME NEW p \in sent',
              p.type = "2a"
      PROVE  \E Q \in Quorums,
                S \in SUBSET {m \in sent' : m.type = "1b" /\ m.bal = p.bal} :
                /\ \A a \in Q : \E m \in S : m.acc = a
                /\ \/ \A m \in S : m.maxVBal = -1
                   \/ \E c \in 0..(p.bal-1) :
                        /\ \A m \in S : m.maxVBal =< c
                        /\ \E m \in S : /\ m.maxVBal = c
                                        /\ m.maxVal = p.val
  <2>1. p \in sent
    BY <1>3, SMT
  <2>2. PICK Q \in Quorums,
              S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = p.bal} :
           /\ \A a \in Q : \E m \in S : m.acc = a
           /\ \/ \A m \in S : m.maxVBal = -1
              \/ \E c \in 0..(p.bal-1) :
                   /\ \A m \in S : m.maxVBal =< c
                   /\ \E m \in S : /\ m.maxVBal = c
                                   /\ m.maxVal = p.val
    BY <1>1, <1>3, <2>1 DEF ProposalInv
  <2>3. S \in SUBSET {m \in sent' : m.type = "1b" /\ m.bal = p.bal}
    BY <2>2, SMT
  <2>4. QED
    BY <2>2, <2>3
<1>4. QED
  BY <1>2, <1>3

THEOREM PromiseInvAdd2b ==
  ASSUME PromiseInv,
         NEW newMsg,
         sent' = sent \cup {newMsg},
         newMsg.type = "2b",
         newMsg.bal \in Int,
         \A m \in sent : m.type = "1b" => m.bal \in Int,
         \A m \in sent :
           m.type \in {"1b", "2b"} /\ m.acc = newMsg.acc => newMsg.bal >= m.bal
  PROVE  PromiseInv'
PROOF
<1>1. PromiseInv
  OBVIOUS
<1>2. \A m \in sent :
          m.type \in {"1b", "2b"} /\ m.acc = newMsg.acc => newMsg.bal >= m.bal
  OBVIOUS
<1>3. SUFFICES ASSUME NEW p \in sent',
                       p.type = "1b"
                PROVE  /\ p.maxVBal = -1 \/ VotedForIn(p.acc, p.maxVal, p.maxVBal)'
                       /\ \A n \in sent' :
                            n.type = "2b" /\ n.acc = p.acc /\ n.bal < p.bal
                              => n.bal <= p.maxVBal
  BY DEF PromiseInv
<1>4. ASSUME NEW p \in sent',
              p.type = "1b"
      PROVE  /\ p.maxVBal = -1 \/ VotedForIn(p.acc, p.maxVal, p.maxVBal)'
             /\ \A n \in sent' :
                  n.type = "2b" /\ n.acc = p.acc /\ n.bal < p.bal
                    => n.bal <= p.maxVBal
  <2>1. p \in sent
    BY <1>4, SMT
  <2>2. p.maxVBal = -1 \/ VotedForIn(p.acc, p.maxVal, p.maxVBal)
    BY <1>1, <2>1, <1>4 DEF PromiseInv
  <2>3. p.maxVBal = -1 \/ VotedForIn(p.acc, p.maxVal, p.maxVBal)'
    BY <2>2, SMT DEF VotedForIn
  <2>4. \A n \in sent' :
           n.type = "2b" /\ n.acc = p.acc /\ n.bal < p.bal
             => n.bal <= p.maxVBal
    <3>1. SUFFICES ASSUME NEW n \in sent',
                           n.type = "2b" /\ n.acc = p.acc /\ n.bal < p.bal
                    PROVE  n.bal <= p.maxVBal
      OBVIOUS
    <3>2. ASSUME NEW n \in sent',
                  n.type = "2b" /\ n.acc = p.acc /\ n.bal < p.bal
          PROVE  n.bal <= p.maxVBal
      <4>1. CASE n \in sent
        BY <1>1, <2>1, <1>4, <3>2, <4>1 DEF PromiseInv
      <4>2. CASE n = newMsg
        <5>1. newMsg.acc = p.acc /\ newMsg.bal = n.bal
          BY <3>2, <4>2
        <5>2. newMsg.bal >= p.bal
          BY <1>2, <2>1, <1>4, <5>1
        <5>3. newMsg.bal < p.bal
          BY <3>2, <4>2
        <5>4. newMsg.bal \in Int /\ p.bal \in Int
          BY <2>1, <1>4, SMT
        <5>5. FALSE
          BY <5>2, <5>3, <5>4, SimpleArithmetic
        <5>6. QED
          BY <5>5
      <4>3. QED
        BY <3>2, <4>1, <4>2, SMT
    <3>3. QED
      BY <3>1, <3>2
  <2>5. QED
    BY <2>3, <2>4
<1>5. QED
  BY <1>3, <1>4

THEOREM ProposalSafeStep ==
  IndInv => \A b \in Nat : (\A d \in 0..(b-1) : SafeAtBallot(d)) => SafeAtBallot(b)
PROOF
<1>1. ASSUME IndInv
      PROVE  \A b \in Nat : (\A d \in 0..(b-1) : SafeAtBallot(d)) => SafeAtBallot(b)
  <2>1. \A b \in Nat : (\A d \in 0..(b-1) : SafeAtBallot(d)) => SafeAtBallot(b)
    <3>1. SUFFICES ASSUME NEW b \in Nat,
                           \A d \in 0..(b-1) : SafeAtBallot(d)
                    PROVE  SafeAtBallot(b)
      OBVIOUS
    <3>2. ASSUME NEW b \in Nat,
                  \A d \in 0..(b-1) : SafeAtBallot(d)
          PROVE  SafeAtBallot(b)
      <4>1. SUFFICES ASSUME NEW p \in sent,
                             p.type = "2a" /\ p.bal = b
                      PROVE  SafeAt(b, p.val)
        BY DEF SafeAtBallot
      <4>2. ASSUME NEW p \in sent,
                    p.type = "2a" /\ p.bal = b
            PROVE  SafeAt(b, p.val)
        <5>1. PICK Q \in Quorums,
                    S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = p.bal} :
                 /\ \A a \in Q : \E m \in S : m.acc = a
                 /\ \/ \A m \in S : m.maxVBal = -1
                    \/ \E d \in 0..(p.bal-1) :
                         /\ \A m \in S : m.maxVBal =< d
                         /\ \E m \in S : /\ m.maxVBal = d
                                         /\ m.maxVal = p.val
          BY <1>1, <4>2 DEF IndInv, ProposalInv
        <5>2. SUFFICES ASSUME NEW c \in 0..(b-1),
                              NEW w \in Values,
                              ChosenIn(w, c)
                       PROVE  w = p.val
          BY DEF SafeAt
        <5>3. ASSUME NEW c \in 0..(b-1),
                      NEW w \in Values,
                      ChosenIn(w, c)
              PROVE  w = p.val
          <6>1. PICK Qc \in Quorums :
                   \A a \in Qc : VotedForIn(a, w, c)
            BY <5>3 DEF ChosenIn
          <6>2. PICK a \in Q \cap Qc : TRUE
            BY <5>1, <6>1, QuorumAssumption
          <6>3. PICK s \in S : s.acc = a
            BY <5>1, <6>2
          <6>4. VotedForIn(a, w, c)
            BY <6>1, <6>2
          <6>5. s \in sent /\ s.type = "1b" /\ s.bal = b
            BY <5>1, <6>3, <4>2, SMT
          <6>6. PICK n \in sent : /\ n.type = "2b"
                                    /\ n.val = w
                                    /\ n.bal = c
                                    /\ n.acc = a
            BY <6>4 DEF VotedForIn
          <6>7. c < s.bal
            BY <5>3, <6>5, SMT
          <6>8. c <= s.maxVBal
            BY <1>1, <6>3, <6>5, <6>6, <6>7, PromiseLower
          <6>9. CASE \A m \in S : m.maxVBal = -1
            BY <5>3, <6>3, <6>8, <6>9, SMT
          <6>10. CASE \E d \in 0..(p.bal-1) :
                         /\ \A m \in S : m.maxVBal =< d
                         /\ \E m \in S : /\ m.maxVBal = d
                                         /\ m.maxVal = p.val
            <7>1. PICK d \in 0..(p.bal-1) :
                    /\ \A m \in S : m.maxVBal =< d
                    /\ \E m \in S : /\ m.maxVBal = d
                                    /\ m.maxVal = p.val
              BY <6>10
            <7>2. PICK t \in S : /\ t.maxVBal = d
                                  /\ t.maxVal = p.val
              BY <7>1
            <7>3. s.maxVBal <= d
              BY <6>3, <7>1, SMT
            <7>4. c \in Int /\ s.maxVBal \in Int /\ d \in Int
              BY <1>1, <5>3, <6>5, <7>1 DEF IndInv, MsgInv, Ballots
            <7>5. c <= d
              BY <6>8, <7>3, <7>4, LeqTrans
            <7>6. CASE c = d
              <8>1. VotedForIn(t.acc, p.val, c)
                BY <1>1, <5>1, <7>2, <7>6 DEF IndInv, PromiseInv
              <8>2. QED
                BY <6>4, <8>1, VoteValueUnique, <1>1
            <7>7. CASE c < d
              <8>1. VotedForIn(t.acc, p.val, d)
                BY <1>1, <5>1, <7>2 DEF IndInv, PromiseInv
              <8>2. PICK pp \in sent : /\ pp.type = "2a"
                                      /\ pp.bal = d
                                      /\ pp.val = p.val
                BY <1>1, <8>1 DEF IndInv, VoteInv, VotedForIn
              <8>3. d \in 0..(b-1)
                BY <4>2, <7>1, SMT
              <8>4. SafeAtBallot(d)
                BY <3>2, <8>3
              <8>5. SafeAt(d, p.val)
                BY <8>2, <8>4 DEF SafeAtBallot
              <8>6. QED
                BY <5>3, <7>7, <8>5 DEF SafeAt
            <7>8. QED
              BY <7>5, <7>6, <7>7, SMT
          <6>11. QED
            BY <5>1, <6>9, <6>10
        <5>4. QED
          BY <5>2, <5>3
      <4>3. QED
        BY <4>1, <4>2
    <3>3. QED
      BY <3>1, <3>2
  <2>2. QED
    BY <2>1
<1>2. QED
  BY <1>1

THEOREM ProposalSafe ==
  IndInv => \A b \in Ballots : SafeAtBallot(b)
PROOF
<1>1. ASSUME IndInv
      PROVE  \A b \in Ballots : SafeAtBallot(b)
  <2>. DEFINE P(n) == SafeAtBallot(n)
  <2>1. \A b \in Nat : P(b)
    <3>1. ASSUME NEW b \in Nat,
                  \A d \in 0..(b-1) : P(d)
          PROVE  P(b)
      <4>1. \A d \in 0..(b-1) : SafeAtBallot(d)
        BY <3>1 DEF P
      <4>2. SafeAtBallot(b)
        BY <1>1, <3>1, <4>1, ProposalSafeStep
      <4>3. QED
        BY <4>2 DEF P
    <3>. HIDE DEF P
    <3>. QED
      BY <3>1, GeneralNatInduction, Blast
  <2>2. QED
    BY <2>1 DEF P, Ballots
<1>2. QED
  BY <1>1

THEOREM IndInvInit == Init => IndInv
PROOF
  BY SMT DEF Init, IndInv, MsgInv, TypeOK, Unique2a, VoteInv, PromiseInv, ProposalInv,
             VotedForIn

THEOREM IndInvNext == IndInv /\ [Next]_vars => IndInv'
PROOF
<1>1. ASSUME IndInv, [Next]_vars
      PROVE  IndInv'
  <2>1. CASE vars' = vars
    BY <1>1, <2>1
       DEF IndInv, MsgInv, TypeOK, Unique2a, VoteInv, PromiseInv, ProposalInv,
           vars, VotedForIn
  <2>2. CASE Next
    <3>1. CASE \E b \in Ballots : Phase1a(b)
      <4>1. PICK b \in Ballots : Phase1a(b)
        BY <3>1
      <4>2. QED
        BY <1>1, <4>1, Isa
           DEF IndInv, MsgInv, TypeOK, Unique2a, VoteInv, PromiseInv, ProposalInv,
               Phase1a, Send, VotedForIn, Ballots
    <3>2. CASE \E b \in Ballots : Phase2a(b)
      <4>1. PICK b \in Ballots : Phase2a(b)
        BY <3>2
      <4>2. PICK v \in Values,
                  Q \in Quorums,
                  S \in SUBSET {mm \in sent : mm.type = "1b" /\ mm.bal = b} :
               /\ ~ \E mm \in sent : mm.type = "2a" /\ mm.bal = b
               /\ \A a \in Q : \E mm \in S : mm.acc = a
               /\ \/ \A mm \in S : mm.maxVBal = -1
                  \/ \E c \in 0..(b-1) :
                       /\ \A mm \in S : mm.maxVBal =< c
                       /\ \E mm \in S : /\ mm.maxVBal = c
                                       /\ mm.maxVal = v
               /\ Send([type |-> "2a", bal |-> b, val |-> v])
        BY <4>1 DEF Phase2a
      <4>. DEFINE new == [type |-> "2a", bal |-> b, val |-> v]
      <4>3. MsgInv'
        BY <1>1, <4>2, SMT
           DEF IndInv, MsgInv, Send, Ballots
      <4>4. Unique2a'
        BY <1>1, <4>2, SMT
           DEF IndInv, Unique2a, Send, new
      <4>5. VoteInv'
        BY <1>1, <4>2, SMT
           DEF IndInv, VoteInv, Send
      <4>6. PromiseInv'
        BY <1>1, <4>2, SMT
           DEF IndInv, PromiseInv, Send, VotedForIn
      <4>7. ProposalInv'
        <5>1. SUFFICES ASSUME NEW p \in sent',
                               p.type = "2a"
                        PROVE  \E QQ \in Quorums,
                                  SS \in SUBSET {mm \in sent' :
                                                 mm.type = "1b" /\ mm.bal = p.bal} :
                                  /\ \A aa \in QQ : \E mm \in SS : mm.acc = aa
                                  /\ \/ \A mm \in SS : mm.maxVBal = -1
                                     \/ \E c \in 0..(p.bal-1) :
                                          /\ \A mm \in SS : mm.maxVBal =< c
                                          /\ \E mm \in SS : /\ mm.maxVBal = c
                                                          /\ mm.maxVal = p.val
          BY DEF ProposalInv
        <5>2. ASSUME NEW p \in sent',
                      p.type = "2a"
              PROVE  \E QQ \in Quorums,
                        SS \in SUBSET {mm \in sent' :
                                       mm.type = "1b" /\ mm.bal = p.bal} :
                        /\ \A aa \in QQ : \E mm \in SS : mm.acc = aa
                        /\ \/ \A mm \in SS : mm.maxVBal = -1
                           \/ \E c \in 0..(p.bal-1) :
                                /\ \A mm \in SS : mm.maxVBal =< c
                                /\ \E mm \in SS : /\ mm.maxVBal = c
                                                /\ mm.maxVal = p.val
          <6>1. CASE p \in sent
            <7>1. PICK QQ \in Quorums,
                        SS \in SUBSET {mm \in sent :
                                       mm.type = "1b" /\ mm.bal = p.bal} :
                     /\ \A aa \in QQ : \E mm \in SS : mm.acc = aa
                     /\ \/ \A mm \in SS : mm.maxVBal = -1
                        \/ \E c \in 0..(p.bal-1) :
                             /\ \A mm \in SS : mm.maxVBal =< c
                             /\ \E mm \in SS : /\ mm.maxVBal = c
                                             /\ mm.maxVal = p.val
              BY <1>1, <5>2, <6>1 DEF IndInv, ProposalInv
            <7>2. SS \in SUBSET {mm \in sent' : mm.type = "1b" /\ mm.bal = p.bal}
              BY <4>2, <7>1 DEF Send
            <7>3. QED
              BY <7>1, <7>2
          <6>2. CASE p = new
            <7>1. S \in SUBSET {mm \in sent' : mm.type = "1b" /\ mm.bal = p.bal}
              BY <4>2, <6>2 DEF Send, new
            <7>2. QED
              BY <4>2, <6>2, <7>1 DEF new
          <6>3. QED
            BY <4>2, <5>2, <6>1, <6>2 DEF Send, new
        <5>3. QED
          BY <5>1, <5>2
      <4>8. QED
        BY <4>3, <4>4, <4>5, <4>6, <4>7 DEF IndInv
    <3>3. CASE \E a \in Acceptors : Phase1b(a)
      <4>1. PICK a \in Acceptors : Phase1b(a)
        BY <3>3
      <4>2. PICK m \in sent, r \in last_voted(a) :
               /\ m.type = "1a"
               /\ \A m2 \in sent :
                    m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal > m2.bal
               /\ Send([type |-> "1b",
                        bal |-> m.bal,
                        maxVBal |-> r.bal,
                        maxVal |-> r.val,
                        acc |-> a])
        BY <4>1 DEF Phase1b
      <4>. DEFINE new == [type |-> "1b",
                          bal |-> m.bal,
                          maxVBal |-> r.bal,
                          maxVal |-> r.val,
                          acc |-> a]
      <4>3. MsgInv'
        BY <1>1, <4>1, <4>2, LastVotedProps, SMT
           DEF IndInv, MsgInv, Send, Ballots
      <4>4. Unique2a'
        BY <1>1, <4>2, SMT
           DEF IndInv, Unique2a, Send
      <4>5. VoteInv'
        BY <1>1, <4>2, SMT
           DEF IndInv, VoteInv, Send
      <4>6. PromiseInv'
        BY <1>1, <4>1, <4>2, LastVotedProps, SMT
           DEF IndInv, PromiseInv, Send, VotedForIn, Ballots
      <4>7. ProposalInv'
        BY <1>1, <4>2, ProposalInvAddNon2a
           DEF IndInv, Send, new
      <4>8. QED
        BY <4>3, <4>4, <4>5, <4>6, <4>7 DEF IndInv
    <3>4. CASE \E a \in Acceptors : Phase2b(a)
      <4>1. PICK a \in Acceptors : Phase2b(a)
        BY <3>4
      <4>2. PICK m \in sent :
               /\ m.type = "2a"
               /\ \A m2 \in sent :
                    m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal >= m2.bal
               /\ Send([type |-> "2b",
                        bal |-> m.bal,
                        val |-> m.val,
                        acc |-> a])
        BY <4>1 DEF Phase2b
      <4>. DEFINE new == [type |-> "2b",
                          bal |-> m.bal,
                          val |-> m.val,
                          acc |-> a]
      <4>3. MsgInv'
        BY <1>1, <4>1, <4>2, SMT
           DEF IndInv, MsgInv, Send, Ballots
      <4>4. Unique2a'
        BY <1>1, <4>2, SMT
           DEF IndInv, Unique2a, Send
      <4>5. VoteInv'
        BY <1>1, <4>2, SMT
           DEF IndInv, VoteInv, Send, new
      <4>6. PromiseInv'
        BY <1>1, <4>2, PromiseInvAdd2b
           DEF IndInv, MsgInv, Send, new, Ballots
      <4>7. ProposalInv'
        BY <1>1, <4>2, ProposalInvAddNon2a
           DEF IndInv, Send, new
      <4>8. QED
        BY <4>3, <4>4, <4>5, <4>6, <4>7 DEF IndInv
    <3>5. QED
      BY <2>2, <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>3. QED
    BY <1>1, <2>1, <2>2 DEF vars
<1>2. QED
  BY <1>1

THEOREM IndInvConsistency == IndInv => Consistency
PROOF
<1>1. ASSUME IndInv
      PROVE  Consistency
  <2>1. SUFFICES ASSUME NEW v1 \in Values,
                         NEW v2 \in Values,
                         Chosen(v1) /\ Chosen(v2)
                  PROVE  v1 = v2
    BY DEF Consistency
  <2>2. ASSUME NEW v1 \in Values,
                NEW v2 \in Values,
                Chosen(v1) /\ Chosen(v2)
        PROVE  v1 = v2
    <3>1. PICK b1 \in Ballots : ChosenIn(v1, b1)
      BY <2>2 DEF Chosen
    <3>2. PICK b2 \in Ballots : ChosenIn(v2, b2)
      BY <2>2 DEF Chosen
    <3>3. CASE b1 = b2
      <4>1. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
        BY <3>1 DEF ChosenIn
      <4>2. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
        BY <3>2 DEF ChosenIn
      <4>3. PICK a \in Q1 \cap Q2 : TRUE
        BY <4>1, <4>2, QuorumAssumption
      <4>4. /\ VotedForIn(a, v1, b1)
             /\ VotedForIn(a, v2, b1)
        BY <3>3, <4>1, <4>2, <4>3
      <4>5. QED
        BY <1>1, <4>4, VoteValueUnique
    <3>4. CASE b1 < b2
      <4>1. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
        BY <3>2 DEF ChosenIn
      <4>2. PICK a \in Q2 : TRUE
        BY <4>1, QuorumAssumption
      <4>3. VotedForIn(a, v2, b2)
        BY <4>1, <4>2
      <4>4. PICK p \in sent : /\ p.type = "2a"
                              /\ p.bal = b2
                              /\ p.val = v2
        BY <1>1, <4>3 DEF IndInv, VoteInv, VotedForIn
      <4>5. SafeAtBallot(b2)
        BY <1>1, <3>2, ProposalSafe
      <4>6. SafeAt(b2, v2)
        BY <4>4, <4>5 DEF SafeAtBallot
      <4>7. b1 \in 0..(b2-1)
        BY <3>1, <3>2, <3>4, SMT DEF Ballots
      <4>8. v1 = v2
        BY <2>2, <3>1, <4>6, <4>7 DEF SafeAt
      <4>9. QED
        BY <4>8
    <3>5. CASE b2 < b1
      <4>1. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
        BY <3>1 DEF ChosenIn
      <4>2. PICK a \in Q1 : TRUE
        BY <4>1, QuorumAssumption
      <4>3. VotedForIn(a, v1, b1)
        BY <4>1, <4>2
      <4>4. PICK p \in sent : /\ p.type = "2a"
                              /\ p.bal = b1
                              /\ p.val = v1
        BY <1>1, <4>3 DEF IndInv, VoteInv, VotedForIn
      <4>5. SafeAtBallot(b1)
        BY <1>1, <3>1, ProposalSafe
      <4>6. SafeAt(b1, v1)
        BY <4>4, <4>5 DEF SafeAtBallot
      <4>7. b2 \in 0..(b1-1)
        BY <3>1, <3>2, <3>5, SMT DEF Ballots
      <4>8. v2 = v1
        BY <2>2, <3>2, <4>6, <4>7 DEF SafeAt
      <4>9. QED
        BY <4>8
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, SMT DEF Ballots
  <2>3. QED
    BY <2>1, <2>2
<1>2. QED
  BY <1>1

THEOREM Consistent == Spec => []Consistency
PROOF
<1>1. Spec => []IndInv
  BY IndInvInit, IndInvNext, PTL DEF Spec
<1>2. []IndInv => []Consistency
  BY IndInvConsistency, PTL
<1>3. QED
  BY <1>1, <1>2, PTL

=============================================================================
