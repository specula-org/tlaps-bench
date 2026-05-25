-----------------MODULE PaxosProof_line91-------------------
EXTENDS TLAPS, PaxosTuple

WellFormedMessages == \A m \in msgs :
    /\ m[1] = "1a" => m[2] \in Ballot
    /\ m[1] = "1b" => /\ m[2] \in Acceptor
                      /\ m[3] \in Ballot
                      /\ m[4] \in Ballot \union {-1}
                      /\ m[5] \in Value \union {None}
    /\ m[1] = "2a" => m[2] \in Ballot /\ m[3] \in Value
    /\ m[1] = "2b" => m[2] \in Acceptor /\ m[3] \in Ballot /\ m[4] \in Value
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

StructOK == /\ TypeOK 
            /\ StructOK1 
            /\ StructOK2 
\*            /\ StructOK3 
            /\ StructOK4 
            /\ StructOK5 


-----------------------------------------------------------------------------
Inv == TypeOK /\ StructOK1 /\ StructOK2 /\ StructOK3 /\ StructOK4 /\ StructOK5

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof scaffolding for the target theorem.                               *)
(***************************************************************************)

\* Type information for "1b" messages, extracted from TypeOK.
LEMMA Msg1bType ==
  ASSUME TypeOK, NEW m \in msgs, m[1] = "1b"
  PROVE  /\ m[2] \in Acceptor
         /\ m[3] \in Ballot
         /\ m[4] \in Ballot \cup {-1}
         /\ m[5] \in Value \cup {None}
  BY DEF TypeOK, Message

\* maxBal is integer-valued on acceptors.
LEMMA MaxBalType ==
  ASSUME TypeOK, NEW x \in Acceptor
  PROVE  maxBal[x] \in Int
  BY DEF TypeOK, Ballot

\* Membership characterization of the derived votes function.
LEMMA VotesDef ==
  ASSUME NEW a \in Acceptor, NEW bb, NEW w
  PROVE  (<<bb, w>> \in votes[a]) <=>
           (\E m \in msgs : m[1] = "2b" /\ m[2] = a /\ m[3] = bb /\ m[4] = w)
  BY DEF votes

\* Core lemma: if value w was proposed (a "2a" message) at some ballot cc that is
\* at least bb, then w is "shown safe at" bb for some quorum.  Proved by strong
\* induction on cc.
LEMMA ShowsSafeFromVote ==
  ASSUME Inv, NEW bb \in Ballot, NEW w \in Value
  PROVE  \A cc \in Ballot :
           (cc >= bb /\ (\E mm \in msgs : mm[1] = "2a" /\ mm[2] = cc /\ mm[3] = w))
           => \E Q2 \in Quorum : V!ShowsSafeAt(Q2, bb, w)
PROOF
<1> USE DEF Ballot
<1> DEFINE P(cc) ==
      (cc >= bb /\ (\E mm \in msgs : mm[1] = "2a" /\ mm[2] = cc /\ mm[3] = w))
      => \E Q2 \in Quorum : V!ShowsSafeAt(Q2, bb, w)
<1>1. \A n \in Nat : (\A mi \in 0..(n-1) : P(mi)) => P(n)
  <2> SUFFICES ASSUME NEW n \in Nat,
                      \A mi \in 0..(n-1) : P(mi),
                      n >= bb,
                      \E mm \in msgs : mm[1] = "2a" /\ mm[2] = n /\ mm[3] = w
               PROVE  \E Q2 \in Quorum : V!ShowsSafeAt(Q2, bb, w)
    BY DEF P
  <2>1. PICK mm \in msgs : mm[1] = "2a" /\ mm[2] = n /\ mm[3] = w
    OBVIOUS
  <2>2. PICK Qn \in Quorum : V!ShowsSafeAt(Qn, n, w)
    BY <2>1 DEF Inv, StructOK3
  <2>3. Qn \subseteq Acceptor
    BY <2>2, QuorumAssumption
  <2>4. \A x \in Qn : maxBal[x] >= n
    BY <2>2 DEF V!ShowsSafeAt
  <2>5. PICK c1 \in -1..(n-1) :
          /\ (c1 # -1) => \E y \in Qn : <<c1, w>> \in votes[y]
          /\ \A d \in (c1+1)..(n-1), y \in Qn : \A vv \in Value : ~(<<d, vv>> \in votes[y])
    BY <2>2 DEF V!ShowsSafeAt, V!VotedFor, V!DidNotVoteAt
  <2>6. \A x \in Qn : maxBal[x] >= bb
    <3> SUFFICES ASSUME NEW x \in Qn PROVE maxBal[x] >= bb
      OBVIOUS
    <3>1. x \in Acceptor BY <2>3
    <3>2. maxBal[x] >= n BY <2>4
    <3>3. maxBal[x] \in Int BY <3>1, MaxBalType DEF Inv
    <3> QED BY <3>2, <3>3, n >= bb
  <2>7. CASE c1 <= bb - 1
    <3>1. c1 \in -1..(bb-1)
      BY <2>5, <2>7
    <3>2. V!ShowsSafeAt(Qn, bb, w)
      <4>1. (c1 # -1) => \E y \in Qn : V!VotedFor(y, c1, w)
        BY <2>5 DEF V!VotedFor
      <4>2. \A d \in (c1+1)..(bb-1), y \in Qn : V!DidNotVoteAt(y, d)
        <5> SUFFICES ASSUME NEW d \in (c1+1)..(bb-1), NEW y \in Qn
                     PROVE  V!DidNotVoteAt(y, d)
          OBVIOUS
        <5>1. d \in (c1+1)..(n-1)
          BY <2>7
        <5> QED BY <5>1, <2>5 DEF V!DidNotVoteAt, V!VotedFor
      <4>3. \E c \in -1..(bb-1) :
              /\ (c # -1) => \E y \in Qn : V!VotedFor(y, c, w)
              /\ \A d \in (c+1)..(bb-1), y \in Qn : V!DidNotVoteAt(y, d)
        <5> WITNESS c1 \in -1..(bb-1)
        <5> QED BY <4>1, <4>2
      <4> QED BY <2>6, <4>3 DEF V!ShowsSafeAt
    <3> QED BY <2>2, <3>2
  <2>8. CASE ~(c1 <= bb - 1)
    <3>1. c1 >= bb /\ c1 # -1
      BY <2>5, <2>8
    <3>2. PICK y \in Qn : <<c1, w>> \in votes[y]
      BY <2>5, <3>1
    <3>3. y \in Acceptor BY <2>3, <3>2
    <3>4. \E m \in msgs : m[1] = "2b" /\ m[2] = y /\ m[3] = c1 /\ m[4] = w
      BY <3>2, <3>3, VotesDef
    <3>5. \E mo \in msgs : mo[1] = "2a" /\ mo[2] = c1 /\ mo[3] = w
      BY <3>4 DEF Inv, StructOK4
    <3>6. c1 \in 0..(n-1)
      BY <2>5, <3>1
    <3>7. P(c1)
      BY <3>6
    <3> QED BY <3>7, <3>1, <3>5 DEF P
  <2> QED BY <2>7, <2>8
<1> HIDE DEF P
<1>2. \A cc \in Nat : P(cc)
  BY ONLY <1>1, GeneralNatInduction, Blast
<1> QED BY <1>2 DEF P

THEOREM \A b \in Ballot, v \in Value :
            Phase2a(b,v) /\ Inv => \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)
PROOF
<1> USE DEF Ballot
<1> SUFFICES ASSUME NEW b \in Ballot, NEW v \in Value, Phase2a(b, v), Inv
             PROVE  \E Q \in Quorum : V!ShowsSafeAt(Q, b, v)
  OBVIOUS
<1> DEFINE Q1b(QQ) == {m \in msgs : m[1] = "1b" /\ m[2] \in QQ /\ m[3] = b}
<1> DEFINE Q1bv(QQ) == {m \in Q1b(QQ) : m[4] \geq 0}
<1>1. PICK Q \in Quorum :
        /\ \A a \in Q : \E m \in Q1b(Q) : m[2] = a
        /\ \/ Q1bv(Q) = {}
           \/ \E m \in Q1bv(Q) : m[5] = v /\ \A mm \in Q1bv(Q) : m[4] \geq mm[4]
  BY DEF Phase2a, Q1b, Q1bv
<1>2. Q \subseteq Acceptor
  BY <1>1, QuorumAssumption
<1>3. \A a \in Q : maxBal[a] >= b
  <2> SUFFICES ASSUME NEW a \in Q PROVE maxBal[a] >= b
    OBVIOUS
  <2>1. PICK m \in Q1b(Q) : m[2] = a
    BY <1>1
  <2>2. m \in msgs /\ m[1] = "1b" /\ m[3] = b
    BY <2>1 DEF Q1b
  <2> QED BY <2>1, <2>2 DEF Inv, StructOK2
<1>4. CASE Q1bv(Q) = {}
  <2>1. V!ShowsSafeAt(Q, b, v)
    <3>1. \A d \in 0..(b-1), a \in Q : V!DidNotVoteAt(a, d)
      <4> SUFFICES ASSUME NEW d \in 0..(b-1), NEW a \in Q
                   PROVE  V!DidNotVoteAt(a, d)
        OBVIOUS
      <4>1. PICK m \in Q1b(Q) : m[2] = a
        BY <1>1
      <4>2. m \in msgs /\ m[1] = "1b" /\ m[2] = a /\ m[3] = b
        BY <4>1 DEF Q1b
      <4>3. ~(m[4] \geq 0)
        BY <4>1, <1>4 DEF Q1bv
      <4>4. m[4] \in Ballot \cup {-1}
        BY <4>2, Msg1bType DEF Inv
      <4>5. m[4] < d
        BY <4>3, <4>4 DEF Ballot
      <4>6. d \in Ballot /\ d < m[3]
        BY <4>2 DEF Ballot
      <4> QED BY <4>2, <4>5, <4>6 DEF Inv, StructOK5, V!DidNotVoteAt, V!VotedFor
    <3>2. \E c \in -1..(b-1) :
            /\ (c # -1) => \E a \in Q : V!VotedFor(a, c, v)
            /\ \A d \in (c+1)..(b-1), a \in Q : V!DidNotVoteAt(a, d)
      <4> WITNESS -1 \in -1..(b-1)
      <4> QED BY <3>1
    <3> QED BY <1>3, <3>2 DEF V!ShowsSafeAt
  <2> QED BY <1>1, <2>1
<1>5. CASE Q1bv(Q) # {}
  <2>1. PICK m0 \in Q1bv(Q) : m0[5] = v /\ \A mm \in Q1bv(Q) : m0[4] \geq mm[4]
    BY <1>1, <1>5
  <2>2. m0 \in msgs /\ m0[1] = "1b" /\ m0[2] \in Q /\ m0[3] = b /\ m0[4] \geq 0
    BY <2>1 DEF Q1bv, Q1b
  <2>3. m0[2] \in Acceptor
    BY <2>2, <1>2
  <2>4. <<m0[4], m0[5]>> \in votes[m0[2]]
    BY <2>2 DEF Inv, StructOK2
  <2>5. m0[4] \in Ballot
    <3>1. m0[4] \in Ballot \cup {-1}
      BY <2>2, Msg1bType DEF Inv
    <3> QED BY <3>1, <2>2 DEF Ballot
  <2>6. <<m0[4], v>> \in votes[m0[2]]
    BY <2>4, <2>1
  <2>7. CASE m0[4] <= b - 1
    <3>1. m0[4] \in -1..(b-1)
      BY <2>5, <2>7 DEF Ballot
    <3>2. V!ShowsSafeAt(Q, b, v)
      <4>1. (m0[4] # -1) => \E a \in Q : V!VotedFor(a, m0[4], v)
        BY <2>2, <2>6 DEF V!VotedFor
      <4>2. \A d \in (m0[4]+1)..(b-1), a \in Q : V!DidNotVoteAt(a, d)
        <5> SUFFICES ASSUME NEW d \in (m0[4]+1)..(b-1), NEW a \in Q
                     PROVE  V!DidNotVoteAt(a, d)
          OBVIOUS
        <5>1. PICK m \in Q1b(Q) : m[2] = a
          BY <1>1
        <5>2. m \in msgs /\ m[1] = "1b" /\ m[2] = a /\ m[3] = b
          BY <5>1 DEF Q1b
        <5>3. m[4] \in Ballot \cup {-1}
          BY <5>2, Msg1bType DEF Inv
        <5>4. m[4] \leq m0[4]
          <6>1. CASE m[4] \geq 0
            <7>1. m \in Q1bv(Q)
              BY <5>1, <6>1 DEF Q1bv
            <7> QED BY <7>1, <2>1
          <6>2. CASE ~(m[4] \geq 0)
            BY <6>2, <5>3, <2>5 DEF Ballot
          <6> QED BY <6>1, <6>2
        <5>5. m[4] < d
          BY <5>4, <2>5, <5>3 DEF Ballot
        <5>6. d \in Ballot /\ d < m[3]
          BY <5>2, <2>5 DEF Ballot
        <5> QED BY <5>2, <5>5, <5>6 DEF Inv, StructOK5, V!DidNotVoteAt, V!VotedFor
      <4>3. \E c \in -1..(b-1) :
              /\ (c # -1) => \E a \in Q : V!VotedFor(a, c, v)
              /\ \A d \in (c+1)..(b-1), a \in Q : V!DidNotVoteAt(a, d)
        <5> WITNESS m0[4] \in -1..(b-1)
        <5> QED BY <4>1, <4>2
      <4> QED BY <1>3, <4>3 DEF V!ShowsSafeAt
    <3> QED BY <1>1, <3>2
  <2>8. CASE ~(m0[4] <= b - 1)
    <3>1. m0[4] >= b
      BY <2>5, <2>8 DEF Ballot
    <3>2. \E m \in msgs : m[1] = "2b" /\ m[2] = m0[2] /\ m[3] = m0[4] /\ m[4] = v
      BY <2>6, <2>3, VotesDef
    <3>3. PICK m2 \in msgs : m2[1] = "2b" /\ m2[2] = m0[2] /\ m2[3] = m0[4] /\ m2[4] = v
      BY <3>2
    <3>4. \E mo \in msgs : mo[1] = "2a" /\ mo[2] = m0[4] /\ mo[3] = v
      BY <3>3 DEF Inv, StructOK4
    <3>5. \A cc \in Ballot :
            (cc >= b /\ (\E mm \in msgs : mm[1] = "2a" /\ mm[2] = cc /\ mm[3] = v))
            => \E Q2 \in Quorum : V!ShowsSafeAt(Q2, b, v)
      BY ShowsSafeFromVote
    <3>6. (m0[4] >= b /\ (\E mm \in msgs : mm[1] = "2a" /\ mm[2] = m0[4] /\ mm[3] = v))
          => \E Q2 \in Quorum : V!ShowsSafeAt(Q2, b, v)
      BY <3>5, <2>5
    <3> QED BY <3>6, <3>1, <3>4
  <2> QED BY <2>7, <2>8
<1> QED BY <1>4, <1>5
------------------------------------------------------------
============================================================