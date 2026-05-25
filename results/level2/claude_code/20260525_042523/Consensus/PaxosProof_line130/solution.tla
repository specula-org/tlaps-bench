-----------------MODULE PaxosProof_line130-------------------
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


------------------------------------------------------------
\* ----- Helper lemmas about the derived operator `votes` -----

\* Adding a message that is not a "2b" message does not change `votes`.
LEMMA VotesUnchanged ==
  ASSUME NEW nm, nm[1] # "2b", msgs' = msgs \cup {nm}
  PROVE  votes' = votes
PROOF
<1>1. \A c \in Acceptor : votes'[c] = votes[c]
  <2> TAKE c \in Acceptor
  <2>1. votes'[c] = {<<mm[3],mm[4]>> : mm \in {m \in msgs' : m[1]="2b" /\ m[2]=c}}
    BY DEF votes
  <2>2. votes[c] = {<<mm[3],mm[4]>> : mm \in {m \in msgs : m[1]="2b" /\ m[2]=c}}
    BY DEF votes
  <2>3. {m \in msgs' : m[1]="2b" /\ m[2]=c} = {m \in msgs : m[1]="2b" /\ m[2]=c}
    OBVIOUS
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>1 DEF votes

\* Adding a "2b" message from acceptor `a` for ballot B / value Vv extends votes[a]
\* by <<B, Vv>> and leaves the others unchanged.
LEMMA VotesChanged ==
  ASSUME NEW a \in Acceptor, NEW B, NEW Vv,
         msgs' = msgs \cup {<<"2b", a, B, Vv>>}
  PROVE  votes' = [votes EXCEPT ![a] = votes[a] \cup {<<B, Vv>>}]
PROOF
<1> DEFINE NM == <<"2b", a, B, Vv>>
<1>a. NM[1] = "2b" /\ NM[2] = a /\ NM[3] = B /\ NM[4] = Vv
  OBVIOUS
<1>dom. DOMAIN votes = Acceptor /\ DOMAIN votes' = Acceptor
  BY DEF votes
<1>1. \A c \in Acceptor : votes'[c] = (IF c = a THEN votes[c] \cup {<<B,Vv>>} ELSE votes[c])
  <2> TAKE c \in Acceptor
  <2>1. votes'[c] = {<<mm[3],mm[4]>> : mm \in {m \in msgs' : m[1]="2b" /\ m[2]=c}}
    BY DEF votes
  <2>2. votes[c] = {<<mm[3],mm[4]>> : mm \in {m \in msgs : m[1]="2b" /\ m[2]=c}}
    BY DEF votes
  <2>3. CASE c = a
    <3>1. {m \in msgs' : m[1]="2b" /\ m[2]=c} = {m \in msgs : m[1]="2b" /\ m[2]=c} \cup {NM}
      BY <1>a, <2>3
    <3>2. {<<mm[3],mm[4]>> : mm \in ({m \in msgs : m[1]="2b" /\ m[2]=c} \cup {NM})}
            = {<<mm[3],mm[4]>> : mm \in {m \in msgs : m[1]="2b" /\ m[2]=c}} \cup {<<NM[3],NM[4]>>}
      OBVIOUS
    <3>3. votes'[c] = votes[c] \cup {<<B,Vv>>}
      BY <2>1, <2>2, <3>1, <3>2, <1>a
    <3> QED BY <3>3, <2>3
  <2>4. CASE c # a
    <3>1. {m \in msgs' : m[1]="2b" /\ m[2]=c} = {m \in msgs : m[1]="2b" /\ m[2]=c}
      BY <1>a, <2>4
    <3>2. votes'[c] = votes[c]
      BY <2>1, <2>2, <3>1
    <3> QED BY <3>2, <2>4
  <2> QED BY <2>3, <2>4
<1>3. votes' = [c \in Acceptor |-> IF c = a THEN votes[c] \cup {<<B,Vv>>} ELSE votes[c]]
  BY <1>1 DEF votes
<1>4. [votes EXCEPT ![a] = votes[a] \cup {<<B,Vv>>}]
        = [c \in Acceptor |-> IF c = a THEN votes[c] \cup {<<B,Vv>>} ELSE votes[c]]
  BY <1>dom
<1> QED BY <1>3, <1>4

------------------------------------------------------------
THEOREM Next /\ Inv => V!Next \/ UNCHANGED <<votes,maxBal>>
PROOF
<1> SUFFICES ASSUME Next, Inv
             PROVE  V!Next \/ UNCHANGED <<votes,maxBal>>
  OBVIOUS
<1>1. CASE \E b \in Ballot : Phase1a(b)
  <2>1. PICK b \in Ballot : Phase1a(b) BY <1>1
  <2>2. msgs' = msgs \cup {<<"1a", b>>} /\ maxBal' = maxBal
    BY <2>1 DEF Phase1a, Send
  <2>3. <<"1a", b>>[1] # "2b" OBVIOUS
  <2>4. votes' = votes BY <2>2, <2>3, VotesUnchanged
  <2> QED BY <2>2, <2>4
<1>2. CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
  <2>1. PICK b \in Ballot, v \in Value : Phase2a(b, v) BY <1>2
  <2>2. msgs' = msgs \cup {<<"2a", b, v>>} /\ maxBal' = maxBal
    BY <2>1 DEF Phase2a, Send
  <2>3. <<"2a", b, v>>[1] # "2b" OBVIOUS
  <2>4. votes' = votes BY <2>2, <2>3, VotesUnchanged
  <2> QED BY <2>2, <2>4
<1>3. CASE \E a \in Acceptor : Phase1b(a)
  <2>1. PICK a \in Acceptor : Phase1b(a) BY <1>3
  <2>2. PICK m \in msgs :
            /\ m[1] = "1a"
            /\ m[2] > maxBal[a]
            /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
            /\ msgs' = msgs \cup {<<"1b", a, m[2], maxVBal[a], maxVal[a]>>}
    BY <2>1 DEF Phase1b, Send
  <2>3. m[2] \in Ballot
    BY <2>2 DEF Inv, TypeOK, Message
  <2>4. <<"1b", a, m[2], maxVBal[a], maxVal[a]>>[1] # "2b" OBVIOUS
  <2>5. votes' = votes BY <2>2, <2>4, VotesUnchanged
  <2>6. V!IncreaseMaxBal(a, m[2])
    BY <2>2, <2>5 DEF V!IncreaseMaxBal
  <2>7. V!Next
    <3>1. \E aa \in Acceptor, bb \in Nat :
              V!IncreaseMaxBal(aa, bb) \/ (\E vv \in Value : V!VoteFor(aa, bb, vv))
      BY <2>6, <2>3 DEF Ballot
    <3> QED BY <3>1 DEF V!Next, V!Ballot
  <2> QED BY <2>7
<1>4. CASE \E a \in Acceptor : Phase2b(a)
  <2>1. PICK a \in Acceptor : Phase2b(a) BY <1>4
  <2>2. PICK m \in msgs :
            /\ m[1] = "2a"
            /\ m[2] \geq maxBal[a]
            /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
            /\ msgs' = msgs \cup {<<"2b", a, m[2], m[3]>>}
    BY <2>1 DEF Phase2b, Send
  <2>3. m[2] \in Ballot /\ m[3] \in Value
    BY <2>2 DEF Inv, TypeOK, Message
  <2>4. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<m[2], m[3]>>}]
    BY <2>2, <2>3, VotesChanged
  <2>dom. DOMAIN votes = Acceptor /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    BY DEF votes, Inv, TypeOK
  <2>5. CASE <<m[2], m[3]>> \in votes[a]
    <3>1. votes[a] \cup {<<m[2], m[3]>>} = votes[a] BY <2>5
    <3>2. votes' = votes
      <4>1. \A c \in Acceptor : votes'[c] = votes[c]
        <5> TAKE c \in Acceptor
        <5>1. votes'[c] = [votes EXCEPT ![a] = votes[a]][c] BY <2>4, <3>1
        <5>2. [votes EXCEPT ![a] = votes[a]][c] = votes[c] BY <2>dom
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>1 DEF votes
    <3>3. PICK x \in msgs : x[1] = "2b" /\ x[2] = a /\ x[3] = m[2]
      BY <2>5 DEF votes
    <3>4. maxBal[a] \geq m[2]
      BY <3>3 DEF Inv, StructOK4
    <3>5. maxBal[a] = m[2]
      BY <3>4, <2>2, <2>3, <2>dom DEF Ballot
    <3>6. maxBal' = maxBal
      BY <2>2, <3>5, <2>dom
    <3> QED BY <3>2, <3>6
  <2>6. CASE <<m[2], m[3]>> \notin votes[a]
    <3>1. maxBal[a] \leq m[2]
      BY <2>2, <2>3, <2>dom DEF Ballot
    <3>2. \A vt \in votes[a] : vt[1] # m[2]
      <4>1. SUFFICES ASSUME NEW vt \in votes[a], vt[1] = m[2] PROVE FALSE
        OBVIOUS
      <4>2. PICK x \in msgs : x[1] = "2b" /\ x[2] = a /\ vt = <<x[3], x[4]>>
        BY <4>1 DEF votes
      <4>3. x[3] = m[2] BY <4>1, <4>2
      <4>4. PICK mo \in msgs : mo[1] = "2a" /\ mo[2] = x[3] /\ mo[3] = x[4]
        BY <4>2 DEF Inv, StructOK4
      <4>5. mo[3] = m[3]
        BY <4>4, <4>3, <2>2 DEF Inv, StructOK3
      <4>6. vt = <<m[2], m[3]>> BY <4>2, <4>3, <4>4, <4>5
      <4> QED BY <4>1, <4>6, <2>6
    <3>3. \A c \in Acceptor \ {a} : \A vt \in votes[c] : (vt[1] = m[2]) => (vt[2] = m[3])
      <4>1. SUFFICES ASSUME NEW c \in Acceptor \ {a}, NEW vt \in votes[c], vt[1] = m[2]
                     PROVE  vt[2] = m[3]
        OBVIOUS
      <4>2. PICK x \in msgs : x[1] = "2b" /\ x[2] = c /\ vt = <<x[3], x[4]>>
        BY <4>1 DEF votes
      <4>3. x[3] = m[2] BY <4>1, <4>2
      <4>4. PICK mo \in msgs : mo[1] = "2a" /\ mo[2] = x[3] /\ mo[3] = x[4]
        BY <4>2 DEF Inv, StructOK4
      <4>5. mo[3] = m[3]
        BY <4>4, <4>3, <2>2 DEF Inv, StructOK3
      <4> QED BY <4>2, <4>4, <4>5
    <3>4. \E Q \in Quorum : V!ShowsSafeAt(Q, m[2], m[3])
      BY <2>2 DEF Inv, StructOK3
    <3>5. V!VoteFor(a, m[2], m[3])
      BY <3>1, <3>2, <3>3, <3>4, <2>4, <2>2 DEF V!VoteFor
    <3>6. V!Next
      <4>1. \E aa \in Acceptor, bb \in Nat :
                V!IncreaseMaxBal(aa, bb) \/ (\E vv \in Value : V!VoteFor(aa, bb, vv))
        BY <3>5, <2>3 DEF Ballot
      <4> QED BY <4>1 DEF V!Next, V!Ballot
    <3> QED BY <3>6
  <2> QED BY <2>5, <2>6
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF Next
============================================================