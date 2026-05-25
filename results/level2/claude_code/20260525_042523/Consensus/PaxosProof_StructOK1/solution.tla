-----------------MODULE PaxosProof_StructOK1-------------------
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

IndInv == TypeOK /\ StructOK1

LEMMA InitIndInv == Init => IndInv
  BY DEF Init, IndInv, TypeOK, StructOK1, Ballot, votes

LEMMA NextIndInv == IndInv /\ [Next]_vars => IndInv'
  <1> SUFFICES ASSUME IndInv, [Next]_vars
               PROVE  IndInv'
    OBVIOUS
  <1> USE DEF IndInv, TypeOK, StructOK1, Ballot
  <1>1. CASE Next
    <2>1. CASE \E b \in Ballot : (Phase1a(b) \/ (\E v \in Value : Phase2a(b, v)))
      <3>1. PICK b \in Ballot : Phase1a(b) \/ (\E v \in Value : Phase2a(b, v))
        BY <2>1
      <3>2. CASE Phase1a(b)
        <4>1. msgs' = msgs \cup {<<"1a", b>>}
          BY <3>2 DEF Phase1a, Send
        <4>2. UNCHANGED <<maxBal, maxVBal, maxVal>>
          BY <3>2 DEF Phase1a
        <4>3. TypeOK'
          BY <4>1, <4>2 DEF Message
        <4>4. votes' = votes
          BY <4>1 DEF votes
        <4>5. StructOK1'
          BY <4>2, <4>4 DEF StructOK1
        <4> QED BY <4>3, <4>5
      <3>3. CASE \E v \in Value : Phase2a(b, v)
        <4>0. PICK v \in Value : Phase2a(b, v)  BY <3>3
        <4>1. msgs' = msgs \cup {<<"2a", b, v>>}
          BY <4>0 DEF Phase2a, Send
        <4>2. UNCHANGED <<maxBal, maxVBal, maxVal>>
          BY <4>0 DEF Phase2a
        <4>3. TypeOK'
          BY <4>1, <4>2 DEF Message
        <4>4. votes' = votes
          BY <4>1 DEF votes
        <4>5. StructOK1'
          BY <4>2, <4>4 DEF StructOK1
        <4> QED BY <4>3, <4>5
      <3> QED BY <3>1, <3>2, <3>3
    <2>2. CASE \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)
      <3>1. PICK a \in Acceptor : Phase1b(a) \/ Phase2b(a)  BY <2>2
      <3>2. CASE Phase1b(a)
        <4>1. PICK m \in msgs :
                /\ m[1] = "1a"
                /\ m[2] > maxBal[a]
                /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
                /\ msgs' = msgs \cup {<<"1b", a, m[2], maxVBal[a], maxVal[a]>>}
          BY <3>2 DEF Phase1b, Send
        <4>2. UNCHANGED <<maxVBal, maxVal>>
          BY <3>2 DEF Phase1b
        <4>3. m[2] \in Ballot
          BY <4>1 DEF Message
        <4>4. TypeOK'
          BY <4>1, <4>2, <4>3 DEF Message
        <4>5. votes' = votes
          BY <4>1 DEF votes
        <4>6. StructOK1'
          BY <4>2, <4>5 DEF StructOK1
        <4> QED BY <4>4, <4>6
      <3>3. CASE Phase2b(a)
        <4>1. PICK m \in msgs :
                /\ m[1] = "2a"
                /\ m[2] \geq maxBal[a]
                /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
                /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
                /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
                /\ msgs' = msgs \cup {<<"2b", a, m[2], m[3]>>}
          BY <3>3 DEF Phase2b, Send
        <4>2. m[2] \in Ballot /\ m[3] \in Value
          BY <4>1 DEF Message
        <4>3. TypeOK'
          BY <4>1, <4>2 DEF Message
        <4>4. StructOK1'
          <5> SUFFICES ASSUME NEW a2 \in Acceptor
                       PROVE  IF maxVBal'[a2] = -1
                              THEN maxVal'[a2] = None
                              ELSE <<maxVBal'[a2], maxVal'[a2]>> \in votes'[a2]
            BY DEF StructOK1
          <5>1. CASE a2 = a
            <6>1. maxVBal'[a2] = m[2] /\ maxVal'[a2] = m[3]
              BY <4>1, <5>1
            <6>2. m[2] # -1
              BY <4>2
            <6>3. <<"2b", a, m[2], m[3]>> \in {mm \in msgs' : mm[1] = "2b" /\ mm[2] = a}
              BY <4>1
            <6>4. <<m[2], m[3]>> \in votes'[a2]
              BY <4>1, <5>1, <6>3 DEF votes
            <6> QED BY <6>1, <6>2, <6>4
          <5>2. CASE a2 # a
            <6>1. maxVBal'[a2] = maxVBal[a2] /\ maxVal'[a2] = maxVal[a2]
              BY <4>1, <5>2
            <6>2. votes'[a2] = votes[a2]
              BY <4>1, <5>2 DEF votes
            <6>3. IF maxVBal[a2] = -1
                  THEN maxVal[a2] = None
                  ELSE <<maxVBal[a2], maxVal[a2]>> \in votes[a2]
              BY DEF StructOK1
            <6> QED BY <6>1, <6>2, <6>3
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>3, <4>4
      <3> QED BY <3>1, <3>2, <3>3
    <2> QED BY <1>1, <2>1, <2>2 DEF Next
  <1>2. CASE vars' = vars
    <2>1. /\ maxBal' = maxBal
          /\ maxVBal' = maxVBal
          /\ maxVal' = maxVal
          /\ msgs' = msgs
      BY <1>2 DEF vars
    <2>2. TypeOK'
      BY <2>1
    <2>3. votes' = votes
      BY <2>1 DEF votes
    <2>4. StructOK1'
      BY <2>1, <2>3 DEF StructOK1
    <2> QED BY <2>2, <2>4
  <1> QED BY <1>1, <1>2 DEF Next

THEOREM Spec => []StructOK1
<1>1. Init => IndInv
  BY InitIndInv
<1>2. IndInv /\ [Next]_vars => IndInv'
  BY NextIndInv
<1>3. IndInv => StructOK1
  BY DEF IndInv
<1>4. Spec => []IndInv
  BY <1>1, <1>2, PTL DEF Spec
<1> QED
  BY <1>3, <1>4, PTL
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
============================================================