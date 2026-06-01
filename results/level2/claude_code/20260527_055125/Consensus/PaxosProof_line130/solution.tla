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

-----------------------------------------------------------------------------
\* Helper lemmas for the proof

LEMMA VotesDef ==
  \A a \in Acceptor :
    votes[a] = {<<m[3], m[4]>> : m \in {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}}
PROOF BY DEF votes

LEMMA VotesPrimedDef ==
  \A a \in Acceptor :
    votes'[a] = {<<m[3], m[4]>> : m \in {mm \in msgs' : mm[1] = "2b" /\ mm[2] = a}}
PROOF BY DEF votes

LEMMA VotesIsFunction ==
  ASSUME TypeOK
  PROVE votes \in [Acceptor -> SUBSET (Ballot \X Value)]
PROOF
  <1>1. \A a \in Acceptor :
          {<<mm[3], mm[4]>> : mm \in {m2 \in msgs : m2[1] = "2b" /\ m2[2] = a}}
          \in SUBSET (Ballot \X Value)
    <2>1. TAKE a \in Acceptor
    <2>2. SUFFICES ASSUME NEW x \in {<<mm[3], mm[4]>> : mm \in {m2 \in msgs : m2[1] = "2b" /\ m2[2] = a}}
                  PROVE x \in Ballot \X Value
          OBVIOUS
    <2>3. PICK mm \in msgs : mm[1] = "2b" /\ mm[2] = a /\ x = <<mm[3], mm[4]>>
          BY <2>2
    <2>4. mm \in Message
          BY <2>3 DEF TypeOK
    <2>5. mm[3] \in Ballot /\ mm[4] \in Value
          BY <2>4, <2>3 DEF Message
    <2>6. QED BY <2>3, <2>5
  <1>2. QED BY <1>1 DEF votes

------------------------------------------------------------
THEOREM Next /\ Inv => V!Next \/ UNCHANGED <<votes,maxBal>>
PROOF
<1> SUFFICES ASSUME Next, Inv
             PROVE V!Next \/ UNCHANGED <<votes, maxBal>>
    OBVIOUS
<1>1. TypeOK
      BY DEF Inv
<1>a. msgs \subseteq Message /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
      BY <1>1 DEF TypeOK
<1>2. CASE \E b \in Ballot : Phase1a(b)
  <2>1. PICK b \in Ballot : Phase1a(b)
        BY <1>2
  <2>2. msgs' = msgs \cup {<<"1a", b>>}
        BY <2>1 DEF Phase1a, Send
  <2>3. maxBal' = maxBal
        BY <2>1 DEF Phase1a
  <2>4. \A a \in Acceptor :
          {mm \in msgs' : mm[1] = "2b" /\ mm[2] = a}
          = {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}
        BY <2>2
  <2>5. votes' = votes
        BY <2>4, VotesDef, VotesPrimedDef DEF votes
  <2>6. QED BY <2>3, <2>5
<1>3. CASE \E a \in Acceptor : Phase1b(a)
  <2>1. PICK a \in Acceptor : Phase1b(a)
        BY <1>3
  <2>2. PICK m \in msgs :
          /\ m[1] = "1a"
          /\ m[2] > maxBal[a]
          /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
          /\ msgs' = msgs \cup {<<"1b", a, m[2], maxVBal[a], maxVal[a]>>}
        BY <2>1 DEF Phase1b, Send
  <2>3. <<"1b", a, m[2], maxVBal[a], maxVal[a]>>[1] = "1b"
        OBVIOUS
  <2>4. \A acc \in Acceptor :
          {mm \in msgs' : mm[1] = "2b" /\ mm[2] = acc}
          = {mm \in msgs : mm[1] = "2b" /\ mm[2] = acc}
        BY <2>2, <2>3
  <2>5. votes' = votes
        BY <2>4, VotesDef, VotesPrimedDef DEF votes
  <2>6. m[2] \in Ballot
        BY <2>2, <1>1 DEF TypeOK, Message, Ballot
  <2>7. V!IncreaseMaxBal(a, m[2])
        BY <2>1, <2>2, <2>5, <2>6 DEF Phase1b, V!IncreaseMaxBal
  <2>8. m[2] \in Nat
        BY <2>6 DEF Ballot
  <2>9. V!Next
        BY <2>1, <2>7, <2>8 DEF V!Next, V!Ballot
  <2>10. QED BY <2>9
<1>4. CASE \E b \in Ballot, v \in Value : Phase2a(b, v)
  <2>1. PICK b \in Ballot, v \in Value : Phase2a(b, v)
        BY <1>4
  <2>2. msgs' = msgs \cup {<<"2a", b, v>>}
        BY <2>1 DEF Phase2a, Send
  <2>3. maxBal' = maxBal
        BY <2>1 DEF Phase2a
  <2>4. <<"2a", b, v>>[1] = "2a"
        OBVIOUS
  <2>5. \A acc \in Acceptor :
          {mm \in msgs' : mm[1] = "2b" /\ mm[2] = acc}
          = {mm \in msgs : mm[1] = "2b" /\ mm[2] = acc}
        BY <2>2, <2>4
  <2>6. votes' = votes
        BY <2>5, VotesDef, VotesPrimedDef DEF votes
  <2>7. QED BY <2>3, <2>6
<1>5. CASE \E a \in Acceptor : Phase2b(a)
  <2>1. PICK a \in Acceptor : Phase2b(a)
        BY <1>5
  <2>2. PICK m \in msgs :
          /\ m[1] = "2a"
          /\ m[2] >= maxBal[a]
          /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
          /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
          /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
          /\ msgs' = msgs \cup {<<"2b", a, m[2], m[3]>>}
        BY <2>1 DEF Phase2b, Send
  <2>3. m \in Message
        BY <2>2, <1>1 DEF TypeOK
  <2>4. m[2] \in Ballot /\ m[3] \in Value
        BY <2>3, <2>2 DEF Message
  <2>5. \A acc \in Acceptor :
          {mm \in msgs' : mm[1] = "2b" /\ mm[2] = acc}
          = IF acc = a
            THEN {mm \in msgs : mm[1] = "2b" /\ mm[2] = acc} \cup {<<"2b", a, m[2], m[3]>>}
            ELSE {mm \in msgs : mm[1] = "2b" /\ mm[2] = acc}
        BY <2>2
  <2>6. votes'[a] = votes[a] \cup {<<m[2], m[3]>>}
    <3>1. {mm \in msgs' : mm[1] = "2b" /\ mm[2] = a}
          = {mm \in msgs : mm[1] = "2b" /\ mm[2] = a} \cup {<<"2b", a, m[2], m[3]>>}
          BY <2>2
    <3>2. votes'[a] = {<<mm[3], mm[4]>> : mm \in {mm \in msgs' : mm[1] = "2b" /\ mm[2] = a}}
          BY VotesPrimedDef
    <3>3. votes[a] = {<<mm[3], mm[4]>> : mm \in {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}}
          BY VotesDef
    <3>4. <<"2b", a, m[2], m[3]>>[3] = m[2] /\ <<"2b", a, m[2], m[3]>>[4] = m[3]
          OBVIOUS
    <3>5. QED BY <3>1, <3>2, <3>3, <3>4
  <2>7. \A acc \in Acceptor : acc # a => votes'[acc] = votes[acc]
    <3>1. TAKE acc \in Acceptor
    <3>2. ASSUME acc # a
          PROVE votes'[acc] = votes[acc]
      <4>1. {mm \in msgs' : mm[1] = "2b" /\ mm[2] = acc}
            = {mm \in msgs : mm[1] = "2b" /\ mm[2] = acc}
            BY <2>2, <3>2
      <4>2. QED BY <4>1, VotesDef, VotesPrimedDef
    <3>3. QED BY <3>2
  <2>8. CASE <<m[2], m[3]>> \in votes[a]
    \* UNCHANGED case
    <3>1. \E mm \in msgs : mm[1] = "2b" /\ mm[2] = a /\ mm[3] = m[2] /\ mm[4] = m[3]
      <4>1. votes[a] = {<<mm[3], mm[4]>> : mm \in {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}}
            BY VotesDef
      <4>2. <<m[2], m[3]>> \in {<<mm[3], mm[4]>> : mm \in {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}}
            BY <2>8, <4>1
      <4>3. QED BY <4>2
    <3>2. PICK mm \in msgs : mm[1] = "2b" /\ mm[2] = a /\ mm[3] = m[2] /\ mm[4] = m[3]
          BY <3>1
    <3>3. StructOK4
          BY DEF Inv
    <3>4. maxBal[a] >= m[2]
          BY <3>2, <3>3 DEF StructOK4
    <3>5. maxBal[a] = m[2]
      <4>1. m[2] >= maxBal[a]
            BY <2>2
      <4>2. maxBal[a] \in Ballot \cup {-1}
            BY <1>1 DEF TypeOK
      <4>3. m[2] \in Ballot
            BY <2>4
      <4>4. QED BY <4>1, <3>4, <4>2, <4>3 DEF Ballot
    <3>6. maxBal' = maxBal
      <4>1. maxBal' = [maxBal EXCEPT ![a] = m[2]]
            BY <2>2
      <4>2. maxBal' = [maxBal EXCEPT ![a] = maxBal[a]]
            BY <4>1, <3>5
      <4>3. maxBal \in [Acceptor -> Ballot \cup {-1}]
            BY <1>1 DEF TypeOK
      <4>4. QED BY <4>2, <4>3
    <3>7. <<"2b", a, m[2], m[3]>> \in msgs
      <4>1. \E mm \in msgs : mm[1] = "2b" /\ mm[2] = a /\ mm[3] = m[2] /\ mm[4] = m[3]
        <5>1. votes[a] = {<<mm[3], mm[4]>> : mm \in {mm2 \in msgs : mm2[1] = "2b" /\ mm2[2] = a}}
              BY VotesDef
        <5>2. <<m[2], m[3]>> \in {<<mm[3], mm[4]>> : mm \in {mm2 \in msgs : mm2[1] = "2b" /\ mm2[2] = a}}
              BY <2>8, <5>1
        <5>3. QED BY <5>2
      <4>2. PICK mm \in msgs : mm[1] = "2b" /\ mm[2] = a /\ mm[3] = m[2] /\ mm[4] = m[3]
            BY <4>1
      <4>3. mm \in Message
            BY <4>2, <1>1 DEF TypeOK
      <4>4. mm \in {"2b"} \X Acceptor \X Ballot \X Value
            BY <4>3, <4>2 DEF Message
      <4>5. mm = <<mm[1], mm[2], mm[3], mm[4]>>
            BY <4>4
      <4>6. mm = <<"2b", a, m[2], m[3]>>
            BY <4>2, <4>5
      <4>7. QED BY <4>2, <4>6
    <3>8. msgs' = msgs
          BY <2>2, <3>7
    <3>9. votes' = votes
          BY <3>8 DEF votes
    <3>10. QED BY <3>6, <3>9
  <2>9. CASE <<m[2], m[3]>> \notin votes[a]
    \* V!VoteFor case
    <3>1. maxBal[a] <= m[2]
      <4>1. m[2] >= maxBal[a]
            BY <2>2
      <4>2. maxBal[a] \in Ballot \cup {-1} /\ m[2] \in Ballot
            BY <1>1, <2>4 DEF TypeOK
      <4>3. QED BY <4>1, <4>2 DEF Ballot
    <3>2. \A vt \in votes[a] : vt[1] # m[2]
      <4>1. SUFFICES ASSUME NEW vt \in votes[a], vt[1] = m[2]
                     PROVE FALSE
            OBVIOUS
      <4>2. PICK mm \in msgs :
              mm[1] = "2b" /\ mm[2] = a /\ vt = <<mm[3], mm[4]>>
        <5>1. vt \in {<<mm[3], mm[4]>> : mm \in {mm2 \in msgs : mm2[1] = "2b" /\ mm2[2] = a}}
              BY <4>1, VotesDef
        <5>2. QED BY <5>1
      <4>3. mm[3] = m[2]
            BY <4>1, <4>2
      <4>4. StructOK4
            BY DEF Inv
      <4>5. \E mo \in msgs : mo[1] = "2a" /\ mo[2] = mm[3] /\ mo[3] = mm[4]
            BY <4>2, <4>4 DEF StructOK4
      <4>6. PICK mo \in msgs : mo[1] = "2a" /\ mo[2] = mm[3] /\ mo[3] = mm[4]
            BY <4>5
      <4>7. StructOK3
            BY DEF Inv
      <4>8. mo[2] = m[2]
            BY <4>3, <4>6
      <4>9. m \in msgs /\ m[1] = "2a"
            BY <2>2
      <4>10. mo[3] = m[3]
            BY <4>7, <4>8, <4>9, <4>6 DEF StructOK3
      <4>11. mm[4] = m[3]
             BY <4>6, <4>10
      <4>12. vt = <<m[2], m[3]>>
             BY <4>2, <4>3, <4>11
      <4>13. <<m[2], m[3]>> \in votes[a]
             BY <4>12, <4>1
      <4>14. QED BY <4>13, <2>9
    <3>3. \A c \in Acceptor \ {a} :
            \A vt \in votes[c] : vt[1] = m[2] => vt[2] = m[3]
      <4>1. SUFFICES
              ASSUME NEW c \in Acceptor \ {a},
                     NEW vt \in votes[c],
                     vt[1] = m[2]
              PROVE vt[2] = m[3]
            OBVIOUS
      <4>2. PICK mm \in msgs :
              mm[1] = "2b" /\ mm[2] = c /\ vt = <<mm[3], mm[4]>>
        <5>1. vt \in {<<mm[3], mm[4]>> : mm \in {mm2 \in msgs : mm2[1] = "2b" /\ mm2[2] = c}}
              BY <4>1, VotesDef
        <5>2. QED BY <5>1
      <4>3. mm[3] = m[2]
            BY <4>1, <4>2
      <4>4. StructOK4
            BY DEF Inv
      <4>5. \E mo \in msgs : mo[1] = "2a" /\ mo[2] = mm[3] /\ mo[3] = mm[4]
            BY <4>2, <4>4 DEF StructOK4
      <4>6. PICK mo \in msgs : mo[1] = "2a" /\ mo[2] = mm[3] /\ mo[3] = mm[4]
            BY <4>5
      <4>7. StructOK3
            BY DEF Inv
      <4>8. mo[2] = m[2]
            BY <4>3, <4>6
      <4>9. m \in msgs /\ m[1] = "2a"
            BY <2>2
      <4>10. mo[3] = m[3]
             BY <4>7, <4>8, <4>9, <4>6 DEF StructOK3
      <4>11. mm[4] = m[3]
             BY <4>6, <4>10
      <4>12. vt[2] = mm[4]
             BY <4>2
      <4>13. QED BY <4>11, <4>12
    <3>4. \E Q \in Quorum : V!ShowsSafeAt(Q, m[2], m[3])
      <4>1. StructOK3
            BY DEF Inv
      <4>2. m \in msgs /\ m[1] = "2a"
            BY <2>2
      <4>3. QED BY <4>1, <4>2 DEF StructOK3
    <3>5. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<m[2], m[3]>>}]
      <4>1. votes \in [Acceptor -> SUBSET (Ballot \X Value)]
            BY VotesIsFunction DEF Inv
      <4>2. votes = [acc \in Acceptor |-> votes[acc]]
            BY <4>1
      <4>3. [votes EXCEPT ![a] = votes[a] \cup {<<m[2], m[3]>>}] =
            [acc \in Acceptor |-> IF acc = a THEN votes[a] \cup {<<m[2], m[3]>>} ELSE votes[acc]]
            BY <4>2
      <4>4. \A acc \in Acceptor :
              votes'[acc] = IF acc = a THEN votes[a] \cup {<<m[2], m[3]>>} ELSE votes[acc]
        <5>1. TAKE acc \in Acceptor
        <5>2. CASE acc = a
              BY <2>6, <5>2
        <5>3. CASE acc # a
              BY <2>7, <5>3
        <5>4. QED BY <5>2, <5>3
      <4>5. votes' = [acc \in Acceptor |-> votes'[acc]]
            BY DEF votes
      <4>6. votes' = [acc \in Acceptor |-> IF acc = a THEN votes[a] \cup {<<m[2], m[3]>>} ELSE votes[acc]]
            BY <4>4, <4>5
      <4>7. QED BY <4>3, <4>6
    <3>6. maxBal' = [maxBal EXCEPT ![a] = m[2]]
          BY <2>2
    <3>7. V!VoteFor(a, m[2], m[3])
          BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF V!VoteFor
    <3>8. m[2] \in Nat
          BY <2>4 DEF Ballot
    <3>9. V!Next
          BY <2>1, <3>7, <3>8, <2>4 DEF V!Next, V!Ballot
    <3>10. QED BY <3>9
  <2>10. QED BY <2>8, <2>9
<1>6. QED BY <1>2, <1>3, <1>4, <1>5 DEF Next
============================================================
