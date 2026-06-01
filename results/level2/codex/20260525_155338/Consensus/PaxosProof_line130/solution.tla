-----------------MODULE PaxosProof_line130-------------------
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

------------------------------------------------------------
LEMMA SendNon2bLeavesVotes ==
  ASSUME NEW m, Send(m), m[1] # "2b"
  PROVE  votes' = votes
PROOF
  <1>1. \A a \in Acceptor :
          {<<mm[3], mm[4]>> : mm \in {mmm \in msgs' :
             /\ mmm[1] = "2b"
             /\ mmm[2] = a}}
        =
          {<<mm[3], mm[4]>> : mm \in {mmm \in msgs :
             /\ mmm[1] = "2b"
             /\ mmm[2] = a}}
    BY SMT DEF Send
  <1>2. votes' = votes
    BY <1>1 DEF votes
  <1> QED BY <1>2

LEMMA Send2bUpdatesVotes ==
  ASSUME NEW a \in Acceptor,
         NEW b,
         NEW v,
         Send(<<"2b", a, b, v>>)
  PROVE  votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
PROOF
  <1>1. \A c \in Acceptor :
          {<<mm[3], mm[4]>> : mm \in {mmm \in msgs' :
             /\ mmm[1] = "2b"
             /\ mmm[2] = c}}
        =
          IF c = a
          THEN {<<mm[3], mm[4]>> : mm \in {mmm \in msgs :
                 /\ mmm[1] = "2b"
                 /\ mmm[2] = c}} \cup {<<b, v>>}
          ELSE {<<mm[3], mm[4]>> : mm \in {mmm \in msgs :
                 /\ mmm[1] = "2b"
                 /\ mmm[2] = c}}
    BY SMT DEF Send
  <1>2. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    BY <1>1 DEF votes
  <1> QED BY <1>2

LEMMA Phase1aStep ==
  ASSUME NEW b \in Ballot, Phase1a(b)
  PROVE  UNCHANGED <<votes, maxBal>>
PROOF
  <1>1. votes' = votes BY SendNon2bLeavesVotes DEF Phase1a
  <1>2. maxBal' = maxBal BY DEF Phase1a
  <1> QED BY <1>1, <1>2

LEMMA Phase2aStep ==
  ASSUME NEW b \in Ballot, NEW v \in Value, Phase2a(b, v)
  PROVE  UNCHANGED <<votes, maxBal>>
PROOF
  <1>1. votes' = votes BY SendNon2bLeavesVotes DEF Phase2a
  <1>2. maxBal' = maxBal BY DEF Phase2a
  <1> QED BY <1>1, <1>2

LEMMA IncreaseMaxBalIsVNext ==
  ASSUME NEW a \in Acceptor,
         NEW b \in Ballot,
         V!IncreaseMaxBal(a, b)
  PROVE  V!Next
PROOF
  <1> QED BY DEF V!Next, V!Ballot, Ballot

LEMMA VoteForIsVNext ==
  ASSUME NEW a \in Acceptor,
         NEW b \in Ballot,
         NEW v \in Value,
         V!VoteFor(a, b, v)
  PROVE  V!Next
PROOF
  <1> QED BY DEF V!Next, V!Ballot, Ballot

LEMMA Phase1bStep ==
  ASSUME NEW a \in Acceptor, Phase1b(a), Inv
  PROVE  V!Next
PROOF
  <1>1. PICK m \in msgs :
          /\ m[1] = "1a"
          /\ m[2] > maxBal[a]
          /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
          /\ Send(<<"1b", a, m[2], maxVBal[a], maxVal[a]>>)
    BY DEF Phase1b
  <1>2. m \in Message BY <1>1 DEF Inv, TypeOK
  <1>3. m[2] \in Ballot BY <1>1, <1>2 DEF Message
  <1>4. votes' = votes BY <1>1, SendNon2bLeavesVotes
  <1>5. V!IncreaseMaxBal(a, m[2])
    BY <1>1, <1>4 DEF V!IncreaseMaxBal
  <1> QED BY <1>3, <1>5, IncreaseMaxBalIsVNext

LEMMA ExceptSameVotes ==
  ASSUME NEW a \in Acceptor,
         NEW x,
         x \in votes[a]
  PROVE  [votes EXCEPT ![a] = votes[a] \cup {x}] = votes
PROOF
  <1>1. votes[a] \cup {x} = votes[a] OBVIOUS
  <1> QED BY <1>1 DEF votes

LEMMA ExceptSameMaxBal ==
  ASSUME NEW a \in Acceptor, Inv
  PROVE  [maxBal EXCEPT ![a] = maxBal[a]] = maxBal
PROOF
  <1>1. maxBal \in [Acceptor -> Ballot \cup {-1}] BY DEF Inv, TypeOK
  <1> QED BY <1>1

LEMMA PriorVoteAtBallotMaxBal ==
  ASSUME NEW a \in Acceptor,
         NEW b \in Ballot,
         Inv,
         \E vt \in votes[a] : vt[1] = b
  PROVE  maxBal[a] >= b
PROOF
  <1>1. PICK vt \in votes[a] : vt[1] = b
    OBVIOUS
  <1>2. PICK mm \in {mx \in msgs : /\ mx[1] = "2b"
                                    /\ mx[2] = a} :
          vt = <<mm[3], mm[4]>>
    BY <1>1 DEF votes
  <1>3. /\ mm \in msgs
        /\ mm[1] = "2b"
        /\ mm[2] = a
        /\ mm[3] = b
    BY <1>1, <1>2
  <1> QED BY <1>3 DEF Inv, StructOK4

LEMMA PriorVoteAtBallotIsSame ==
  ASSUME NEW a \in Acceptor,
         NEW b \in Ballot,
         NEW v \in Value,
         NEW m \in msgs,
         m[1] = "2a",
         m[2] = b,
         m[3] = v,
         Inv,
         \E vt \in votes[a] : vt[1] = b
  PROVE  <<b, v>> \in votes[a]
PROOF
  <1>1. PICK vt \in votes[a] : vt[1] = b
    OBVIOUS
  <1>2. PICK mm \in {mx \in msgs : /\ mx[1] = "2b"
                                    /\ mx[2] = a} :
          vt = <<mm[3], mm[4]>>
    BY <1>1 DEF votes
  <1>3. /\ mm \in msgs
        /\ mm[1] = "2b"
        /\ mm[2] = a
        /\ mm[3] = b
    BY <1>1, <1>2
  <1>4. PICK mo \in msgs :
          /\ mo[1] = "2a"
          /\ mo[2] = b
          /\ mo[3] = mm[4]
    BY <1>3 DEF Inv, StructOK4
  <1>5. mm[4] = v BY <1>4 DEF Inv, StructOK3
  <1> QED BY <1>2, <1>3, <1>5 DEF votes

LEMMA Phase2bStep ==
  ASSUME NEW a \in Acceptor, Phase2b(a), Inv
  PROVE  V!Next \/ UNCHANGED <<votes, maxBal>>
PROOF
  <1>1. PICK m \in msgs :
          /\ m[1] = "2a"
          /\ m[2] \geq maxBal[a]
          /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
          /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
          /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
          /\ Send(<<"2b", a, m[2], m[3]>>)
    BY DEF Phase2b
  <1>2. m \in Message BY <1>1 DEF Inv, TypeOK
  <1>3. /\ m[2] \in Ballot
        /\ m[3] \in Value
    BY <1>1, <1>2 DEF Message
  <1>4. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<m[2], m[3]>>}]
    BY <1>1, <1>3, Send2bUpdatesVotes
  <1>5. CASE \A vt \in votes[a] : vt[1] # m[2]
    <2>1. \A c \in Acceptor \ {a} :
            \A vt \in votes[c] : (vt[1] = m[2]) => (vt[2] = m[3])
      BY <1>1 DEF Inv, StructOK3, StructOK4, votes
    <2>2. \E Q \in Quorum : V!ShowsSafeAt(Q, m[2], m[3])
      BY <1>1 DEF Inv, StructOK3
    <2>3. V!VoteFor(a, m[2], m[3])
      BY <1>1, <1>4, <1>5, <2>1, <2>2 DEF V!VoteFor
    <2> QED BY <1>3, <2>3, VoteForIsVNext
  <1>6. CASE ~(\A vt \in votes[a] : vt[1] # m[2])
    <2>1. \E vt \in votes[a] : vt[1] = m[2] BY <1>6
    <2>2. <<m[2], m[3]>> \in votes[a]
      BY <1>1, <1>3, <2>1, PriorVoteAtBallotIsSame
    <2>3a. maxBal[a] >= m[2]
      BY <1>3, <2>1, PriorVoteAtBallotMaxBal
    <2>3b. m[2] >= maxBal[a] BY <1>1
    <2>3c. m[2] \in Int BY <1>3 DEF Ballot
    <2>3d. maxBal[a] \in Ballot \cup {-1}
      BY DEF Inv, TypeOK
    <2>3e. maxBal[a] \in Int BY <2>3d DEF Ballot
    <2>3. maxBal[a] = m[2]
      BY <2>3a, <2>3b, <2>3c, <2>3e, SMT
    <2>4. votes' = votes BY <1>4, <2>2, ExceptSameVotes
    <2>5. maxBal' = maxBal BY <1>1, <2>3, ExceptSameMaxBal
    <2> QED BY <2>4, <2>5
  <1> QED BY <1>5, <1>6

THEOREM Next /\ Inv => V!Next \/ UNCHANGED <<votes,maxBal>>
PROOF
  <1>1. ASSUME Next /\ Inv
        PROVE  V!Next \/ UNCHANGED <<votes, maxBal>>
  PROOF
    <2>1. CASE \E b \in Ballot : Phase1a(b)
      <3>1. PICK b \in Ballot : Phase1a(b) BY <2>1
      <3>2. UNCHANGED <<votes, maxBal>> BY <3>1, Phase1aStep
      <3> QED BY <3>2
    <2>2. CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
      <3>1. PICK b \in Ballot, v \in Value : Phase2a(b, v) BY <2>2
      <3>2. UNCHANGED <<votes, maxBal>> BY <3>1, Phase2aStep
      <3> QED BY <3>2
    <2>3. CASE \E a \in Acceptor : Phase1b(a)
      <3>1. PICK a \in Acceptor : Phase1b(a) BY <2>3
      <3>2. V!Next BY <1>1, <3>1, Phase1bStep
      <3> QED BY <3>2
    <2>4. CASE \E a \in Acceptor : Phase2b(a)
      <3>1. PICK a \in Acceptor : Phase2b(a) BY <2>4
      <3>2. V!Next \/ UNCHANGED <<votes, maxBal>>
        BY <1>1, <3>1, Phase2bStep
      <3> QED BY <3>2
    <2> QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF Next
  <1> QED BY <1>1
============================================================
