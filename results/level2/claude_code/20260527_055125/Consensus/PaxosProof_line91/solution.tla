-----------------MODULE PaxosProof_line91-------------------
EXTENDS TLAPS, PaxosTuple, NaturalsInduction

-----------------------------------------------------------------------------

-----------------------------------------------------------
StructOK1 == \A a \in Acceptor : IF maxVBal[a] = -1
                                 THEN maxVal[a] = None
                                 ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

-----------------------------------------------------------
StructOK2 == \A m \in msgs :
   (m[1] = "1b") => /\ maxBal[m[2]] >= m[3]
                    /\ (m[4] >= 0) => <<m[4],m[5]>> \in votes[m[2]]

StructOK3 == \A m \in msgs : m[1] = "2a" => /\ \E Q \in Quorum : V!ShowsSafeAt(Q,m[2],m[3])
                                            /\ \A mm \in msgs : /\ mm[1] = "2a"
                                                                /\ mm[2] = m[2]
                                                                => mm[3] = m[3]

StructOK4 == \A m \in msgs : m[1] = "2b" => /\ \E mo \in msgs : /\ mo[1] = "2a"
                                                                /\ mo[2] = m[3]
                                                                /\ mo[3] = m[4]
                                            /\ maxBal[m[2]] >= m[3]
                                            /\ maxVBal[m[2]] >= m[3]

StructOK5 == \A m \in msgs : m[1] = "1b" => \A d \in Ballot : m[4] < d /\ d < m[3] =>
                                            \A v \in Value : ~ <<d,v>> \in votes[m[2]]

-----------------------------------------------------------------------------
Inv == TypeOK /\ StructOK1 /\ StructOK2 /\ StructOK3 /\ StructOK4 /\ StructOK5

-----------------------------------------------------------------------------
\* Helper lemmas

LEMMA QuorumIntersect ==
  ASSUME NEW Q1 \in Quorum, NEW Q2 \in Quorum
  PROVE  Q1 \cap Q2 # {}
BY QuorumAssumption

LEMMA QuorumSubsetAcceptor ==
  ASSUME NEW Q \in Quorum
  PROVE  Q \subseteq Acceptor
BY QuorumAssumption

LEMMA VotedForImplies2b ==
  ASSUME NEW a \in Acceptor,
         NEW cc, NEW vv,
         <<cc, vv>> \in votes[a]
  PROVE  \E m \in msgs : /\ m[1] = "2b"
                        /\ m[2] = a
                        /\ m[3] = cc
                        /\ m[4] = vv
BY DEF votes

LEMMA TwoBImpliesTwoA ==
  ASSUME Inv,
         NEW m \in msgs,
         m[1] = "2b"
  PROVE  \E mo \in msgs : /\ mo[1] = "2a"
                         /\ mo[2] = m[3]
                         /\ mo[3] = m[4]
BY DEF Inv, StructOK4

LEMMA VotedForImpliesTwoA ==
  ASSUME Inv,
         NEW a \in Acceptor,
         NEW cc, NEW vv,
         <<cc, vv>> \in votes[a]
  PROVE  \E mo \in msgs : /\ mo[1] = "2a"
                         /\ mo[2] = cc
                         /\ mo[3] = vv
<1>1. \E m \in msgs : /\ m[1] = "2b"
                     /\ m[2] = a
                     /\ m[3] = cc
                     /\ m[4] = vv
  BY VotedForImplies2b
<1>2. QED
  BY <1>1, TwoBImpliesTwoA

LEMMA TwoAImpliesShowsSafe ==
  ASSUME Inv,
         NEW mo \in msgs,
         mo[1] = "2a"
  PROVE  \E Q \in Quorum : V!ShowsSafeAt(Q, mo[2], mo[3])
BY DEF Inv, StructOK3

LEMMA MaxBalType ==
  ASSUME Inv, NEW a \in Acceptor
  PROVE  maxBal[a] \in Ballot \cup {-1}
BY DEF Inv, TypeOK

-----------------------------------------------------------------------------
\* The strong induction predicate
SafetyChainPred(bb) ==
   \A vv \in Value :
      (\E mo \in msgs : /\ mo[1] = "2a"
                        /\ mo[2] = bb
                        /\ mo[3] = vv)
      => \A b2 \in 0..bb : \E Q \in Quorum : V!ShowsSafeAt(Q, b2, vv)

\* The key inductive lemma: if a 2a at ballot bb for vv exists, then for any
\* b2 <= bb, there is a quorum showing vv safe at b2.
LEMMA SafetyChainStep ==
  ASSUME Inv,
         NEW bb \in Nat,
         \A k \in 0..(bb-1) : SafetyChainPred(k)
  PROVE  SafetyChainPred(bb)
<1>1. SUFFICES ASSUME NEW vv \in Value,
                      \E mo \in msgs : /\ mo[1] = "2a"
                                       /\ mo[2] = bb
                                       /\ mo[3] = vv
               PROVE  \A b2 \in 0..bb : \E Q \in Quorum : V!ShowsSafeAt(Q, b2, vv)
  BY DEF SafetyChainPred
<1>2. PICK mo0 \in msgs : /\ mo0[1] = "2a"
                          /\ mo0[2] = bb
                          /\ mo0[3] = vv
  BY <1>1
<1>3. PICK Q0 \in Quorum : V!ShowsSafeAt(Q0, bb, vv)
  <2>1. \E Q \in Quorum : V!ShowsSafeAt(Q, mo0[2], mo0[3])
    BY <1>2, TwoAImpliesShowsSafe
  <2>2. QED BY <2>1, <1>2
<1>4. /\ \A a \in Q0 : maxBal[a] >= bb
      /\ \E c \in -1..(bb-1) :
          /\ (c # -1) => \E a \in Q0 : V!VotedFor(a, c, vv)
          /\ \A d \in (c+1)..(bb-1), a \in Q0 : V!DidNotVoteAt(a, d)
  BY <1>3 DEF V!ShowsSafeAt
<1>5. PICK c \in -1..(bb-1) :
            /\ (c # -1) => \E a \in Q0 : V!VotedFor(a, c, vv)
            /\ \A d \in (c+1)..(bb-1), a \in Q0 : V!DidNotVoteAt(a, d)
  BY <1>4
<1>6. TAKE b2 \in 0..bb
<1>7. CASE b2 = bb
  BY <1>3, <1>7
<1>8. CASE b2 < bb
  <2>1. b2 \in Nat /\ bb \in Nat /\ b2 < bb /\ b2 >= 0
    BY <1>8
  <2>0. c \in Int /\ b2 \in Int /\ bb \in Int
    BY <1>5, <2>1
  <2>2. CASE c < b2
    <3>1. \A a \in Q0 : maxBal[a] >= b2
      <4>1. \A a \in Q0 : maxBal[a] >= bb
        BY <1>4
      <4>2. \A a \in Q0 : a \in Acceptor
        BY QuorumSubsetAcceptor
      <4>3. \A a \in Q0 : maxBal[a] \in Ballot \cup {-1}
        BY <4>2 DEF Inv, TypeOK
      <4>4. bb >= b2
        BY <2>1
      <4>5. QED BY <4>1, <4>3, <4>4 DEF Ballot
    <3>2. (c # -1) => \E a \in Q0 : V!VotedFor(a, c, vv)
      BY <1>5
    <3>3. \A d \in (c+1)..(b2-1), a \in Q0 : V!DidNotVoteAt(a, d)
      <4>1. \A d \in (c+1)..(b2-1) : d \in (c+1)..(bb-1)
        BY <2>1, <2>0
      <4>2. QED BY <1>5, <4>1
    <3>4. c \in -1..(b2-1)
      <4>1. c \in Int /\ c >= -1 /\ c < b2
        BY <1>5, <2>2, <2>0
      <4>2. QED BY <4>1, <2>1
    <3>5. V!ShowsSafeAt(Q0, b2, vv)
      BY <3>1, <3>2, <3>3, <3>4 DEF V!ShowsSafeAt
    <3>6. QED BY <3>5
  <2>3. CASE c >= b2
    <3>1. c # -1
      BY <2>3, <2>1, <2>0
    <3>2. PICK a0 \in Q0 : V!VotedFor(a0, c, vv)
      BY <1>5, <3>1
    <3>3. <<c, vv>> \in votes[a0]
      BY <3>2 DEF V!VotedFor
    <3>4. a0 \in Acceptor
      BY <1>3, QuorumSubsetAcceptor
    <3>5. \E mo \in msgs : /\ mo[1] = "2a"
                          /\ mo[2] = c
                          /\ mo[3] = vv
      BY <3>3, <3>4, VotedForImpliesTwoA
    <3>6. c \in 0..(bb-1)
      <4>1. c >= 0
        BY <3>1, <1>5, <2>3, <2>1, <2>0
      <4>2. c <= bb - 1
        BY <1>5, <2>0, <2>1
      <4>3. QED BY <4>1, <4>2, <2>0, <2>1
    <3>7. SafetyChainPred(c)
      BY <3>6
    <3>8. \A b3 \in 0..c : \E Q \in Quorum : V!ShowsSafeAt(Q, b3, vv)
      BY <3>5, <3>7 DEF SafetyChainPred
    <3>9. b2 \in 0..c
      BY <2>3, <2>1, <2>0
    <3>10. QED BY <3>8, <3>9
  <2>4. QED BY <2>2, <2>3, <2>0
<1>9. b2 \in Int /\ bb \in Int /\ b2 <= bb
  BY <1>6
<1>10. QED BY <1>7, <1>8, <1>9

LEMMA SafetyChain ==
  ASSUME Inv
  PROVE  \A bb \in Nat : SafetyChainPred(bb)
<1> DEFINE Strg(nn) == \A k \in 0..nn : SafetyChainPred(k)
<1>1. \A bb \in Nat : (\A k \in 0..(bb-1) : SafetyChainPred(k)) => SafetyChainPred(bb)
  BY SafetyChainStep
<1>2. Strg(0)
  <2>1. \A k \in 0..0 : SafetyChainPred(k)
    <3>1. TAKE k \in 0..0
    <3>2. k = 0
      OBVIOUS
    <3>3. 0..(0-1) = {}
      OBVIOUS
    <3>4. \A m \in 0..(0-1) : SafetyChainPred(m)
      BY <3>3
    <3>5. SafetyChainPred(0)
      BY <3>4, <1>1
    <3>6. QED BY <3>2, <3>5
  <2>2. QED BY <2>1
<1>3. \A n \in Nat : Strg(n) => Strg(n+1)
  <2>1. TAKE n \in Nat
  <2>2. ASSUME Strg(n)
        PROVE Strg(n+1)
    <3>1. \A m \in 0..n : SafetyChainPred(m)
      BY <2>2
    <3>2. \A m \in 0..((n+1)-1) : SafetyChainPred(m)
      <4>1. (n+1)-1 = n
        OBVIOUS
      <4>2. QED BY <3>1, <4>1
    <3>3. SafetyChainPred(n+1)
      BY <3>2, <1>1
    <3>4. TAKE k \in 0..(n+1)
    <3>5. CASE k \in 0..n
      BY <3>1, <3>5
    <3>6. CASE k = n+1
      BY <3>3, <3>6
    <3>7. k \in 0..n \/ k = n+1
      BY <3>4
    <3>8. QED BY <3>5, <3>6, <3>7
  <2>3. QED BY <2>2
<1>4. HIDE DEF Strg
<1>5. \A n \in Nat : Strg(n)
  BY <1>2, <1>3, NatInduction, Isa
<1>6. QED
  <2>1. TAKE bb \in Nat
  <2>2. Strg(bb)
    BY <1>5
  <2>3. bb \in 0..bb
    OBVIOUS
  <2>4. QED
    BY <2>2, <2>3 DEF Strg

-----------------------------------------------------------------------------
THEOREM \A b \in Ballot, v \in Value :
            Phase2a(b,v) /\ Inv => \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)
<1>1. SUFFICES ASSUME NEW b \in Ballot, NEW v \in Value,
                      Phase2a(b, v), Inv
               PROVE  \E Q \in Quorum : V!ShowsSafeAt(Q, b, v)
  OBVIOUS
<1> DEFINE Q1bf(Q) == {m \in msgs : /\ m[1] = "1b"
                                    /\ m[2] \in Q
                                    /\ m[3] = b}
<1> DEFINE Q1bvf(Q) == {m \in Q1bf(Q) : m[4] \geq 0}
<1>2. PICK Q \in Quorum :
        /\ \A a \in Q : \E m \in Q1bf(Q) : m[2] = a
        /\ \/ Q1bvf(Q) = {}
           \/ \E m \in Q1bvf(Q) :
                /\ m[5] = v
                /\ \A mm \in Q1bvf(Q) : m[4] \geq mm[4]
  BY <1>1 DEF Phase2a
<1> DEFINE Q1b == Q1bf(Q)
<1> DEFINE Q1bv == Q1bvf(Q)
<1>3. /\ \A a \in Q : \E m \in Q1b : m[2] = a
      /\ \/ Q1bv = {}
         \/ \E m \in Q1bv :
              /\ m[5] = v
              /\ \A mm \in Q1bv : m[4] \geq mm[4]
  BY <1>2
<1>4. Q \subseteq Acceptor
  BY QuorumSubsetAcceptor
<1>5. b \in Nat
  BY DEF Ballot
<1>6. \A a \in Q : maxBal[a] >= b
  <2>1. TAKE a \in Q
  <2>2. PICK m \in Q1b : m[2] = a
    BY <1>3
  <2>3. m \in msgs /\ m[1] = "1b" /\ m[3] = b
    BY <2>2
  <2>4. maxBal[m[2]] >= m[3]
    BY <2>3, <1>1 DEF Inv, StructOK2
  <2>5. QED BY <2>2, <2>4
<1>7. CASE Q1bv = {}
  <2>1. \A d \in 0..(b-1), a \in Q : V!DidNotVoteAt(a, d)
    <3>1. TAKE d \in 0..(b-1), a \in Q
    <3>2. PICK m \in Q1b : m[2] = a
      BY <1>3
    <3>3. m \in Q1b
      BY <3>2
    <3>4. m \notin Q1bv
      BY <1>7
    <3>5. m \in msgs /\ m[1] = "1b" /\ m[2] = a /\ m[3] = b
      BY <3>2
    <3>6. m[4] \in Ballot \cup {-1}
      BY <3>5, <1>1 DEF Inv, TypeOK, Message
    <3>7. ~ (m[4] >= 0)
      <4>1. m \in Q1b /\ ~ (m \in Q1bv)
        BY <3>3, <3>4
      <4>2. ~ (m[4] >= 0)
        BY <4>1
      <4>3. QED BY <4>2
    <3>8. m[4] = -1
      BY <3>6, <3>7 DEF Ballot
    <3>9. \A d2 \in Ballot : m[4] < d2 /\ d2 < m[3] => \A v2 \in Value : ~ <<d2, v2>> \in votes[m[2]]
      BY <3>5, <1>1 DEF Inv, StructOK5
    <3>10. d \in Ballot /\ d \in Nat /\ d >= 0 /\ d <= b - 1
      BY <3>1, <1>5 DEF Ballot
    <3>11. m[4] < d /\ d < m[3]
      <4>1. m[4] = -1
        BY <3>8
      <4>2. m[3] = b
        BY <3>5
      <4>3. -1 < d
        BY <3>10
      <4>4. d < b
        BY <3>10, <1>5
      <4>5. QED BY <4>1, <4>2, <4>3, <4>4
    <3>12. \A v2 \in Value : ~ <<d, v2>> \in votes[m[2]]
      BY <3>9, <3>10, <3>11
    <3>13. \A v2 \in Value : ~ V!VotedFor(a, d, v2)
      BY <3>12, <3>5 DEF V!VotedFor
    <3>14. QED BY <3>13 DEF V!DidNotVoteAt
  <2>2. \E c \in -1..(b-1) :
            /\ (c # -1) => \E a \in Q : V!VotedFor(a, c, v)
            /\ \A d \in (c+1)..(b-1), a \in Q : V!DidNotVoteAt(a, d)
    <3>1. -1 \in -1..(b-1)
      BY <1>5
    <3>2. WITNESS -1 \in -1..(b-1)
    <3>3. \A d \in 0..(b-1), a \in Q : V!DidNotVoteAt(a, d)
      BY <2>1
    <3>4. QED BY <3>3
  <2>3. V!ShowsSafeAt(Q, b, v)
    BY <1>6, <2>2 DEF V!ShowsSafeAt
  <2>4. QED BY <2>3
<1>8. CASE Q1bv # {}
  <2>1. PICK m \in Q1bv :
            /\ m[5] = v
            /\ \A mm \in Q1bv : m[4] \geq mm[4]
    BY <1>3, <1>8
  <2>2. /\ m \in Q1b
        /\ m[4] >= 0
    BY <2>1
  <2>3. m \in msgs /\ m[1] = "1b" /\ m[2] \in Q /\ m[3] = b
    BY <2>2
  <2>4. <<m[4], m[5]>> \in votes[m[2]]
    BY <2>3, <2>2, <1>1 DEF Inv, StructOK2
  <2>5. <<m[4], v>> \in votes[m[2]]
    BY <2>4, <2>1
  <2>6. m[2] \in Acceptor
    BY <2>3, <1>4
  <2>7. /\ m[4] \in Ballot \cup {-1}
        /\ m[3] \in Ballot
    BY <2>3, <1>1 DEF Inv, TypeOK, Message
  <2>8. m[4] \in Nat
    BY <2>7, <2>2 DEF Ballot
  <2>9. CASE m[4] < b
    <3>1. m[4] \in 0..(b-1)
      BY <2>8, <2>9, <2>2, <1>5 DEF Ballot
    <3>2. \A d \in (m[4]+1)..(b-1), a \in Q : V!DidNotVoteAt(a, d)
      <4>1. TAKE d \in (m[4]+1)..(b-1), a \in Q
      <4>2. PICK mm \in Q1b : mm[2] = a
        BY <1>3
      <4>3. mm \in msgs /\ mm[1] = "1b" /\ mm[2] = a /\ mm[3] = b
        BY <4>2
      <4>4. /\ mm[4] \in Ballot \cup {-1}
            /\ mm[3] \in Ballot
        BY <4>3, <1>1 DEF Inv, TypeOK, Message
      <4>5. mm[4] <= m[4]
        <5>1. CASE mm \in Q1bv
          <6>1. m[4] >= mm[4]
            BY <5>1, <2>1
          <6>2. QED BY <6>1
        <5>2. CASE mm \notin Q1bv
          <6>1. ~ (mm[4] >= 0)
            BY <5>2, <4>2
          <6>2. mm[4] = -1
            BY <6>1, <4>4 DEF Ballot
          <6>3. -1 <= m[4]
            BY <2>8 DEF Ballot
          <6>4. QED BY <6>2, <6>3
        <5>3. QED BY <5>1, <5>2
      <4>6. \A d2 \in Ballot : mm[4] < d2 /\ d2 < mm[3] => \A v2 \in Value : ~ <<d2, v2>> \in votes[mm[2]]
        BY <4>3, <1>1 DEF Inv, StructOK5
      <4>7. d \in Ballot /\ d \in Nat /\ d >= m[4] + 1 /\ d <= b - 1
        BY <4>1, <2>8, <1>5 DEF Ballot
      <4>8. mm[4] < d
        <5>1. d >= m[4] + 1
          BY <4>7
        <5>2. mm[4] <= m[4]
          BY <4>5
        <5>3. mm[4] \in Int /\ m[4] \in Int /\ d \in Int
          BY <4>4, <2>8, <4>7 DEF Ballot
        <5>4. QED BY <5>1, <5>2, <5>3
      <4>9. d < mm[3]
        <5>1. mm[3] = b
          BY <4>3
        <5>2. d <= b - 1
          BY <4>7
        <5>3. QED BY <5>1, <5>2, <1>5, <4>7
      <4>10. \A v2 \in Value : ~ <<d, v2>> \in votes[mm[2]]
        BY <4>6, <4>7, <4>8, <4>9
      <4>11. \A v2 \in Value : ~ V!VotedFor(a, d, v2)
        BY <4>10, <4>2 DEF V!VotedFor
      <4>12. QED BY <4>11 DEF V!DidNotVoteAt
    <3>3. V!VotedFor(m[2], m[4], v)
      BY <2>5 DEF V!VotedFor
    <3>4. m[4] # -1
      BY <2>2, <2>8 DEF Ballot
    <3>5. \E c \in -1..(b-1) :
              /\ (c # -1) => \E a \in Q : V!VotedFor(a, c, v)
              /\ \A d \in (c+1)..(b-1), a \in Q : V!DidNotVoteAt(a, d)
      <4>1. m[4] \in -1..(b-1)
        BY <3>1, <2>8
      <4>2. WITNESS m[4] \in -1..(b-1)
      <4>3. (m[4] # -1) => \E a \in Q : V!VotedFor(a, m[4], v)
        BY <2>3, <3>3
      <4>4. \A d \in (m[4]+1)..(b-1), a \in Q : V!DidNotVoteAt(a, d)
        BY <3>2
      <4>5. QED BY <4>3, <4>4
    <3>6. V!ShowsSafeAt(Q, b, v)
      BY <1>6, <3>5 DEF V!ShowsSafeAt
    <3>7. QED BY <3>6
  <2>10. CASE m[4] >= b
    <3>1. \E mo \in msgs : /\ mo[1] = "2a"
                          /\ mo[2] = m[4]
                          /\ mo[3] = v
      BY <2>5, <2>6, VotedForImpliesTwoA, <1>1
    <3>2. m[4] \in Nat
      BY <2>8
    <3>3. b \in 0..m[4]
      BY <2>10, <1>5, <2>8
    <3>4. \E Q1 \in Quorum : V!ShowsSafeAt(Q1, b, v)
      BY <3>1, <3>2, <3>3, SafetyChain, <1>1 DEF SafetyChainPred
    <3>5. QED BY <3>4
  <2>11. m[4] < b \/ m[4] >= b
    BY <2>8, <1>5 DEF Ballot
  <2>12. QED BY <2>9, <2>10, <2>11
<1>9. QED BY <1>7, <1>8

------------------------------------------------------------
============================================================
