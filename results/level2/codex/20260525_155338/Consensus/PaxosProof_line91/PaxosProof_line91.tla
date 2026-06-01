-----------------MODULE PaxosProof_line91-------------------
EXTENDS TLAPS, PaxosTuple

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

Q1b(Q,b) == {m \in msgs : /\ m[1] = "1b"
                          /\ m[2] \in Q
                          /\ m[3] = b}

Q1bv(Q,b) == {m \in Q1b(Q,b) : m[4] >= 0}

Phase2aQuorum(Q,b,v) ==
  /\ \A a \in Q : \E m \in Q1b(Q,b) : m[2] = a
  /\ \/ Q1bv(Q,b) = {}
     \/ \E m \in Q1bv(Q,b) :
          /\ m[5] = v
          /\ \A mm \in Q1bv(Q,b) : m[4] >= mm[4]

SafeBefore(b,v) == \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)

VoteAt(b,v) == \E a \in Acceptor : V!VotedFor(a,b,v)

VoteSafeUpTo(n) ==
  \A b \in Ballot, v \in Value :
    /\ b <= n
    /\ VoteAt(n,v)
    /\ Inv
    => SafeBefore(b,v)

LEMMA VotedForMessage ==
  ASSUME NEW a \in Acceptor,
         NEW b \in Ballot,
         NEW v \in Value,
         V!VotedFor(a,b,v)
  PROVE  \E m \in msgs : /\ m[1] = "2b"
                         /\ m[2] = a
                         /\ m[3] = b
                         /\ m[4] = v
PROOF BY SMT DEF V!VotedFor, votes

LEMMA OneBType ==
  ASSUME NEW Q,
         NEW b,
         NEW m \in Q1b(Q,b),
         Inv
  PROVE  /\ m \in msgs
         /\ m[1] = "1b"
         /\ m[2] \in Q
         /\ m[3] = b
         /\ m[4] \in Ballot \cup {-1}
PROOF BY SMT DEF Q1b, Inv, TypeOK, Message

LEMMA ReplyMaxBal ==
  ASSUME NEW Q \in Quorum,
         NEW b \in Ballot,
         Inv,
         \A a \in Q : \E m \in Q1b(Q,b) : m[2] = a
  PROVE  \A a \in Q : maxBal[a] >= b
PROOF
  <1>1. ASSUME NEW a \in Q
          PROVE  maxBal[a] >= b
    <2>1. PICK m \in Q1b(Q,b) : m[2] = a
      OBVIOUS
    <2>2. /\ m \in msgs
           /\ m[1] = "1b"
           /\ m[3] = b
      BY <2>1, OneBType
    <2>3. maxBal[m[2]] >= m[3]
      BY <2>2 DEF Inv, StructOK2
    <2> QED BY <2>1, <2>2, <2>3
  <1> QED BY <1>1

LEMMA ReplyNoVoteAfter ==
  ASSUME NEW Q,
         NEW b,
         NEW m \in Q1b(Q,b),
         NEW d \in Ballot,
         m[4] < d,
         d < b,
         Inv
  PROVE  V!DidNotVoteAt(m[2],d)
PROOF
  <1>1. /\ m \in msgs
         /\ m[1] = "1b"
         /\ m[3] = b
    BY OneBType
  <1>2. \A vv \in Value : ~ <<d,vv>> \in votes[m[2]]
    BY <1>1 DEF Inv, StructOK5
  <1> QED BY <1>2 DEF V!DidNotVoteAt, V!VotedFor

LEMMA EmptyReplyLt ==
  ASSUME NEW Q,
         NEW b,
         NEW m \in Q1b(Q,b),
         Q1bv(Q,b) = {},
         NEW d \in Ballot,
         Inv
  PROVE  m[4] < d
PROOF BY SMT DEF Q1bv, Q1b, Inv, TypeOK, Message, Ballot

LEMMA EmptyQ1bvShowsSafe ==
  ASSUME NEW Q \in Quorum,
         NEW b \in Ballot,
         NEW v \in Value,
         Inv,
         \A a \in Q : \E m \in Q1b(Q,b) : m[2] = a,
         Q1bv(Q,b) = {}
  PROVE  V!ShowsSafeAt(Q,b,v)
PROOF
  <1>1. \A a \in Q : maxBal[a] >= b
    BY ReplyMaxBal
  <1>2. -1 \in -1..(b-1)
    BY SMT DEF Ballot
  <1>3. ASSUME NEW d \in 0..(b-1),
                NEW a \in Q
          PROVE  V!DidNotVoteAt(a,d)
    <2>1. PICK m \in Q1b(Q,b) : m[2] = a
      OBVIOUS
    <2>2. d \in Ballot
      BY SMT DEF Ballot
    <2>3. m[4] < d
      BY <2>1, <2>2, EmptyReplyLt
    <2>4. d < b
      BY SMT DEF Ballot
    <2>5. V!DidNotVoteAt(m[2],d)
      BY <2>1, <2>2, <2>3, <2>4, ReplyNoVoteAfter
    <2> QED BY <2>1, <2>5
  <1>4. \A d \in 0..(b-1), a \in Q : V!DidNotVoteAt(a,d)
    BY <1>3
  <1>5. \E c \in -1..(b-1) :
           /\ (c # -1) => \E a \in Q : V!VotedFor(a,c,v)
           /\ \A d \in (c+1)..(b-1), a \in Q : V!DidNotVoteAt(a,d)
    BY <1>2, <1>4, SMT
  <1> QED BY <1>1, <1>5 DEF V!ShowsSafeAt

LEMMA ReplyLtFromMax ==
  ASSUME NEW Q,
         NEW b,
         NEW top \in Q1bv(Q,b),
         \A mm \in Q1bv(Q,b) : top[4] >= mm[4],
         NEW m \in Q1b(Q,b),
         NEW d \in Ballot,
         top[4] < d,
         Inv
  PROVE  m[4] < d
PROOF BY SMT DEF Q1bv, Q1b, Inv, TypeOK, Message, Ballot

LEMMA Q1bvVote ==
  ASSUME NEW Q,
         NEW b,
         NEW m \in Q1bv(Q,b),
         Inv
  PROVE  /\ m[2] \in Q
         /\ m[4] \in Ballot
         /\ V!VotedFor(m[2],m[4],m[5])
PROOF BY SMT DEF Q1bv, Q1b, Inv, StructOK2, TypeOK, Message, Ballot, V!VotedFor

LEMMA MaxBelowQ1bvShowsSafe ==
  ASSUME NEW Q \in Quorum,
         NEW b \in Ballot,
         NEW v \in Value,
         Inv,
         \A a \in Q : \E m \in Q1b(Q,b) : m[2] = a,
         NEW top \in Q1bv(Q,b),
         top[5] = v,
         \A mm \in Q1bv(Q,b) : top[4] >= mm[4],
         top[4] < b
  PROVE  V!ShowsSafeAt(Q,b,v)
PROOF
  <1>1. \A a \in Q : maxBal[a] >= b
    BY ReplyMaxBal
  <1>2. /\ top[2] \in Q
         /\ top[4] \in Ballot
         /\ V!VotedFor(top[2],top[4],top[5])
    BY Q1bvVote
  <1>3. top[4] \in -1..(b-1)
    BY <1>2, SMT DEF Ballot
  <1>4. \E a \in Q : V!VotedFor(a,top[4],v)
    BY <1>2
  <1>5. ASSUME NEW d \in (top[4]+1)..(b-1),
                NEW a \in Q
          PROVE  V!DidNotVoteAt(a,d)
    <2>1. PICK m \in Q1b(Q,b) : m[2] = a
      OBVIOUS
    <2>2. d \in Ballot
      BY <1>2, SMT DEF Ballot
    <2>3. top[4] < d
      BY <1>2, SMT DEF Ballot
    <2>4. d < b
      BY <1>2, SMT DEF Ballot
    <2>5. m[4] < d
      BY <2>1, <2>2, <2>3, ReplyLtFromMax
    <2>6. V!DidNotVoteAt(m[2],d)
      BY <2>1, <2>2, <2>4, <2>5, ReplyNoVoteAfter
    <2> QED BY <2>1, <2>6
  <1>6. \A d \in (top[4]+1)..(b-1), a \in Q : V!DidNotVoteAt(a,d)
    BY <1>5
  <1>7. \E c \in -1..(b-1) :
           /\ (c # -1) => \E a \in Q : V!VotedFor(a,c,v)
           /\ \A d \in (c+1)..(b-1), a \in Q : V!DidNotVoteAt(a,d)
    BY <1>3, <1>4, <1>6
  <1> QED BY <1>1, <1>7 DEF V!ShowsSafeAt

LEMMA VoteHas2a ==
  ASSUME NEW a \in Acceptor,
         NEW b \in Ballot,
         NEW v \in Value,
         V!VotedFor(a,b,v),
         Inv
  PROVE  \E m \in msgs : /\ m[1] = "2a"
                         /\ m[2] = b
                         /\ m[3] = v
PROOF
  <1>1. PICK mb \in msgs : /\ mb[1] = "2b"
                            /\ mb[2] = a
                            /\ mb[3] = b
                            /\ mb[4] = v
    BY VotedForMessage
  <1>2. \E m \in msgs : /\ m[1] = "2a"
                         /\ m[2] = b
                         /\ m[3] = v
    BY <1>1 DEF Inv, StructOK4
  <1> QED BY <1>2

LEMMA VoteShowsSafe ==
  ASSUME NEW a \in Acceptor,
         NEW b \in Ballot,
         NEW v \in Value,
         V!VotedFor(a,b,v),
         Inv
  PROVE  \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)
PROOF
  <1>1. PICK m \in msgs : /\ m[1] = "2a"
                           /\ m[2] = b
                           /\ m[3] = v
    BY VoteHas2a
  <1>2. \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)
    BY <1>1 DEF Inv, StructOK3
  <1> QED BY <1>2

LEMMA ShowsSafeAtLower ==
  ASSUME NEW Q \in Quorum,
         NEW b \in Ballot,
         NEW c \in Ballot,
         NEW v \in Value,
         b <= c,
         V!ShowsSafeAt(Q,c,v),
         Inv,
         \E e \in -1..(b-1) :
           /\ (e # -1) => \E a \in Q : V!VotedFor(a,e,v)
           /\ \A d \in (e+1)..(c-1), a \in Q : V!DidNotVoteAt(a,d)
  PROVE  V!ShowsSafeAt(Q,b,v)
PROOF
  <1>1. PICK e \in -1..(b-1) :
           /\ (e # -1) => \E a \in Q : V!VotedFor(a,e,v)
           /\ \A d \in (e+1)..(c-1), a \in Q : V!DidNotVoteAt(a,d)
    OBVIOUS
  <1>2. \A a \in Q : maxBal[a] >= c
    BY DEF V!ShowsSafeAt
  <1>3. ASSUME NEW a \in Q
          PROVE  maxBal[a] >= b
    <2>0. a \in Acceptor
      BY QuorumAssumption
    <2>0a. maxBal[a] \in Ballot \cup {-1}
      BY <2>0 DEF Inv, TypeOK
    <2>1. maxBal[a] >= c
      BY <1>2
    <2>2. c >= b
      BY SMT DEF Ballot
    <2> QED BY <2>0a, <2>1, <2>2, SMT DEF Ballot
  <1>4. \A a \in Q : maxBal[a] >= b
    BY <1>3
  <1>5. ASSUME NEW d \in (e+1)..(b-1),
                NEW a \in Q
          PROVE  V!DidNotVoteAt(a,d)
    <2>1. d \in (e+1)..(c-1)
      BY SMT DEF Ballot
    <2> QED BY <1>1, <2>1
  <1>6. \A d \in (e+1)..(b-1), a \in Q : V!DidNotVoteAt(a,d)
    BY <1>5
  <1>7. \E e \in -1..(b-1) :
           /\ (e # -1) => \E a \in Q : V!VotedFor(a,e,v)
           /\ \A d \in (e+1)..(b-1), a \in Q : V!DidNotVoteAt(a,d)
    BY <1>1, <1>6
  <1> QED BY <1>4, <1>7 DEF V!ShowsSafeAt

LEMMA VoteSafeBefore ==
  \A n \in Ballot : VoteSafeUpTo(n)
PROOF
  <1> DEFINE P(n) == VoteSafeUpTo(n)
  <1>1. \A n \in Nat :
           (\A k \in 0..(n-1) : P(k)) => P(n)
  <2>. SUFFICES ASSUME NEW n \in Nat,
                         \A k \in 0..(n-1) : P(k),
                         NEW b \in Ballot,
                         NEW v \in Value,
                         b <= n,
                         VoteAt(n,v),
                         Inv
                  PROVE  SafeBefore(b,v)
      BY DEF P, VoteSafeUpTo, Ballot
  <2>2. PICK a \in Acceptor : V!VotedFor(a,n,v)
    BY DEF VoteAt
  <2>3. PICK Q \in Quorum : V!ShowsSafeAt(Q,n,v)
    BY <2>2, VoteShowsSafe DEF Ballot
  <2>4. CASE b = n
    <3> QED BY <2>3, <2>4 DEF SafeBefore
  <2>5. CASE b # n
    <3>1. b < n
      BY <2>5, SMT DEF Ballot
    <3>2. PICK e \in -1..(n-1) :
             /\ (e # -1) => \E a \in Q : V!VotedFor(a,e,v)
             /\ \A d \in (e+1)..(n-1), a \in Q : V!DidNotVoteAt(a,d)
      BY <2>3 DEF V!ShowsSafeAt
    <3>3. CASE e < b
      <4>1. e \in -1..(b-1)
        BY <3>2, <3>3, SMT DEF Ballot
      <4>2. \E ee \in -1..(b-1) :
               /\ (ee # -1) => \E a \in Q : V!VotedFor(a,ee,v)
               /\ \A d \in (ee+1)..(n-1), a \in Q : V!DidNotVoteAt(a,d)
        BY <3>2, <4>1
      <4>3. V!ShowsSafeAt(Q,b,v)
        BY <2>3, <4>2, ShowsSafeAtLower DEF Ballot
      <4> QED BY <4>3 DEF SafeBefore
    <3>4. CASE e >= b
      <4>1. e # -1
        BY <3>4, SMT DEF Ballot
      <4>2. PICK aa \in Q : V!VotedFor(aa,e,v)
        BY <3>2, <4>1
      <4>3. aa \in Acceptor
        BY QuorumAssumption
      <4>4. e \in 0..(n-1)
        BY <3>2, <3>4, SMT DEF Ballot
      <4>5. e \in Ballot
        BY <4>4 DEF Ballot
      <4>6. VoteAt(e,v)
        BY <4>2, <4>3 DEF VoteAt
      <4>7. VoteSafeUpTo(e)
        BY <4>4 DEF P
      <4>8. SafeBefore(b,v)
        BY <3>4, <4>5, <4>6, <4>7 DEF VoteSafeUpTo
      <4> QED BY <4>8
    <3> QED BY <3>3, <3>4, SMT DEF Ballot
  <2> QED BY <2>4, <2>5
  <1> HIDE DEF P
  <1>2. \A n \in Nat : P(n)
    BY <1>1, GeneralNatInduction, IsaM("blast")
  <1> QED BY <1>2 DEF P, Ballot

LEMMA MaxAtOrAboveSafeBefore ==
  ASSUME NEW Q \in Quorum,
         NEW b \in Ballot,
         NEW v \in Value,
         Inv,
         NEW top \in Q1bv(Q,b),
         top[5] = v,
         top[4] >= b
  PROVE  SafeBefore(b,v)
PROOF
  <1>1. /\ top[2] \in Q
         /\ top[4] \in Ballot
         /\ V!VotedFor(top[2],top[4],top[5])
    BY Q1bvVote
  <1>2. top[2] \in Acceptor
    BY <1>1, QuorumAssumption
  <1>3. VoteAt(top[4],v)
    BY <1>1, <1>2 DEF VoteAt
  <1>4. VoteSafeUpTo(top[4])
    BY <1>1, VoteSafeBefore
  <1> QED BY <1>1, <1>3, <1>4 DEF VoteSafeUpTo

THEOREM \A b \in Ballot, v \in Value : 
            Phase2a(b,v) /\ Inv => \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)
PROOF
  <1>. SUFFICES ASSUME NEW b \in Ballot,
                         NEW v \in Value,
                         Phase2a(b,v),
                         Inv
                  PROVE  SafeBefore(b,v)
    BY DEF SafeBefore
  <1>1. PICK Q \in Quorum : Phase2aQuorum(Q,b,v)
    BY DEF Phase2a, Phase2aQuorum, Q1b, Q1bv
  <1>2. CASE Q1bv(Q,b) = {}
    <2>1. V!ShowsSafeAt(Q,b,v)
      BY <1>1, <1>2, EmptyQ1bvShowsSafe DEF Phase2aQuorum
    <2> QED BY <2>1 DEF SafeBefore
  <1>3. CASE Q1bv(Q,b) # {}
    <2>1. PICK top \in Q1bv(Q,b) :
             /\ top[5] = v
             /\ \A mm \in Q1bv(Q,b) : top[4] >= mm[4]
      BY <1>1, <1>3 DEF Phase2aQuorum
    <2>2. /\ top[2] \in Q
           /\ top[4] \in Ballot
      BY <2>1, Q1bvVote
    <2>3. CASE top[4] < b
      <3>1. V!ShowsSafeAt(Q,b,v)
        BY <1>1, <2>1, <2>3, MaxBelowQ1bvShowsSafe DEF Phase2aQuorum
      <3> QED BY <3>1 DEF SafeBefore
    <2>4. CASE top[4] >= b
      <3>1. SafeBefore(b,v)
        BY <2>1, <2>4, MaxAtOrAboveSafeBefore
      <3> QED BY <3>1
    <2> QED BY <2>2, <2>3, <2>4, SMT DEF Ballot
  <1> QED BY <1>2, <1>3
------------------------------------------------------------
============================================================
