-----------------MODULE PaxosProof_StructOK1-------------------
EXTENDS TLAPS, PaxosTuple

-----------------------------------------------------------------------------

-----------------------------------------------------------
StructOK1 == \A a \in Acceptor : IF maxVBal[a] = -1
                                 THEN maxVal[a] = None
                                 ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

IndInv == TypeOK /\ StructOK1

LEMMA InitInv == Init => IndInv
  <1> SUFFICES ASSUME Init PROVE IndInv OBVIOUS
  <1>1. TypeOK
    BY DEF Init, TypeOK, Ballot
  <1>2. StructOK1
    <2> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  IF maxVBal[a] = -1
                        THEN maxVal[a] = None
                        ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]
      BY DEF StructOK1
    <2>1. maxVBal[a] = -1
      BY DEF Init
    <2>2. maxVal[a] = None
      BY DEF Init
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2 DEF IndInv

LEMMA TypeOKInv == IndInv /\ [Next]_vars => TypeOK'
  <1> SUFFICES ASSUME IndInv, [Next]_vars PROVE TypeOK'
    OBVIOUS
  <1> USE DEF IndInv, TypeOK
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. CASE Next
    <2> USE <1>2 DEF Next
    <2>1. CASE \E b \in Ballot : Phase1a(b)
      BY <2>1 DEF Phase1a, Send, Message
    <2>2. CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
      BY <2>2 DEF Phase2a, Send, Message
    <2>3. CASE \E a \in Acceptor : Phase1b(a)
      <3> SUFFICES ASSUME NEW a \in Acceptor, Phase1b(a)
                   PROVE  TypeOK'
        BY <2>3
      <3>1. PICK m \in msgs : /\ m[1] = "1a"
                              /\ m[2] > maxBal[a]
                              /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
                              /\ Send(<<"1b", a, m[2], maxVBal[a], maxVal[a]>>)
        BY DEF Phase1b
      <3>2. m \in Message
        OBVIOUS
      <3>3. m[2] \in Ballot
        BY <3>1, <3>2 DEF Message
      <3>4. maxBal' \in [Acceptor -> Ballot \cup {-1}]
        BY <3>1, <3>3
      <3>5. UNCHANGED <<maxVBal, maxVal>>
        BY DEF Phase1b
      <3>6. <<"1b", a, m[2], maxVBal[a], maxVal[a]>> \in Message
        BY <3>3 DEF Message
      <3>7. msgs' \subseteq Message
        BY <3>1, <3>6 DEF Send
      <3> QED BY <3>4, <3>5, <3>7
    <2>4. CASE \E a \in Acceptor : Phase2b(a)
      <3> SUFFICES ASSUME NEW a \in Acceptor, Phase2b(a)
                   PROVE  TypeOK'
        BY <2>4
      <3>1. PICK m \in msgs : /\ m[1] = "2a"
                              /\ m[2] \geq maxBal[a]
                              /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
                              /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
                              /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
                              /\ Send(<<"2b", a, m[2], m[3]>>)
        BY DEF Phase2b
      <3>2. m \in Message
        OBVIOUS
      <3>3. m[2] \in Ballot /\ m[3] \in Value
        BY <3>1, <3>2 DEF Message
      <3>4. maxBal' \in [Acceptor -> Ballot \cup {-1}]
        BY <3>1, <3>3
      <3>5. maxVBal' \in [Acceptor -> Ballot \cup {-1}]
        BY <3>1, <3>3
      <3>6. maxVal' \in [Acceptor -> Value \cup {None}]
        BY <3>1, <3>3
      <3>7. <<"2b", a, m[2], m[3]>> \in Message
        BY <3>3 DEF Message
      <3>8. msgs' \subseteq Message
        BY <3>1, <3>7 DEF Send
      <3> QED BY <3>4, <3>5, <3>6, <3>8
    <2> QED BY <2>1, <2>2, <2>3, <2>4
  <1> QED BY <1>1, <1>2

LEMMA StructOK1Inv == IndInv /\ [Next]_vars => StructOK1'
  <1> SUFFICES ASSUME IndInv, [Next]_vars PROVE StructOK1'
    OBVIOUS
  <1> USE DEF IndInv, TypeOK
  <1>1. CASE UNCHANGED vars
    <2>1. \A a \in Acceptor : maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
      BY <1>1 DEF vars
    <2>2. votes' = votes
      BY <1>1 DEF vars, votes
    <2> QED BY <2>1, <2>2 DEF StructOK1
  <1>2. CASE Next
    <2> USE <1>2 DEF Next
    <2>1. CASE \E b \in Ballot : Phase1a(b)
      <3> PICK b \in Ballot : Phase1a(b)
        BY <2>1
      <3>1. UNCHANGED <<maxBal, maxVBal, maxVal>>
        BY DEF Phase1a
      <3>2. \A a \in Acceptor : maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
        BY <3>1
      <3>3. msgs' = msgs \cup {<<"1a", b>>}
        BY DEF Phase1a, Send
      <3>4. \A mm \in msgs' : mm[1] = "2b" => mm \in msgs
        BY <3>3
      <3>5. \A mm \in msgs : mm[1] = "2b" => mm \in msgs'
        BY <3>3
      <3>6. \A a \in Acceptor : votes'[a] = votes[a]
        BY <3>4, <3>5 DEF votes
      <3> QED BY <3>2, <3>6 DEF StructOK1
    <2>2. CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
      <3> PICK b \in Ballot, v \in Value : Phase2a(b, v)
        BY <2>2
      <3>1. UNCHANGED <<maxBal, maxVBal, maxVal>>
        BY DEF Phase2a
      <3>2. \A a \in Acceptor : maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
        BY <3>1
      <3>3. msgs' = msgs \cup {<<"2a", b, v>>}
        BY DEF Phase2a, Send
      <3>4. \A mm \in msgs' : mm[1] = "2b" => mm \in msgs
        BY <3>3
      <3>5. \A mm \in msgs : mm[1] = "2b" => mm \in msgs'
        BY <3>3
      <3>6. \A a \in Acceptor : votes'[a] = votes[a]
        BY <3>4, <3>5 DEF votes
      <3> QED BY <3>2, <3>6 DEF StructOK1
    <2>3. CASE \E a \in Acceptor : Phase1b(a)
      <3> PICK a0 \in Acceptor : Phase1b(a0)
        BY <2>3
      <3>1. PICK m \in msgs : /\ m[1] = "1a"
                              /\ m[2] > maxBal[a0]
                              /\ maxBal' = [maxBal EXCEPT ![a0] = m[2]]
                              /\ Send(<<"1b", a0, m[2], maxVBal[a0], maxVal[a0]>>)
        BY DEF Phase1b
      <3>2. UNCHANGED <<maxVBal, maxVal>>
        BY DEF Phase1b
      <3>3. \A a \in Acceptor : maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
        BY <3>2
      <3>4. msgs' = msgs \cup {<<"1b", a0, m[2], maxVBal[a0], maxVal[a0]>>}
        BY <3>1 DEF Send
      <3>5. \A mm \in msgs' : mm[1] = "2b" => mm \in msgs
        BY <3>4
      <3>6. \A mm \in msgs : mm[1] = "2b" => mm \in msgs'
        BY <3>4
      <3>7. \A a \in Acceptor : votes'[a] = votes[a]
        BY <3>5, <3>6 DEF votes
      <3> QED BY <3>3, <3>7 DEF StructOK1
    <2>4. CASE \E a \in Acceptor : Phase2b(a)
      <3> PICK a0 \in Acceptor : Phase2b(a0)
        BY <2>4
      <3>1. PICK m \in msgs : /\ m[1] = "2a"
                              /\ m[2] \geq maxBal[a0]
                              /\ maxBal' = [maxBal EXCEPT ![a0] = m[2]]
                              /\ maxVBal' = [maxVBal EXCEPT ![a0] = m[2]]
                              /\ maxVal' = [maxVal EXCEPT ![a0] = m[3]]
                              /\ Send(<<"2b", a0, m[2], m[3]>>)
        BY DEF Phase2b
      <3>2. m \in Message
        OBVIOUS
      <3>3. m[2] \in Ballot /\ m[3] \in Value
        BY <3>1, <3>2 DEF Message
      <3>4. m[2] # -1
        BY <3>3 DEF Ballot
      <3>5. msgs' = msgs \cup {<<"2b", a0, m[2], m[3]>>}
        BY <3>1 DEF Send
      <3>6. SUFFICES ASSUME NEW a \in Acceptor
                     PROVE  IF maxVBal'[a] = -1
                            THEN maxVal'[a] = None
                            ELSE <<maxVBal'[a], maxVal'[a]>> \in votes'[a]
        BY DEF StructOK1
      <3>7. CASE a = a0
        <4>1. maxVBal'[a] = m[2]
          BY <3>1, <3>7
        <4>2. maxVal'[a] = m[3]
          BY <3>1, <3>7
        <4>3. maxVBal'[a] # -1
          BY <3>4, <4>1
        <4>4. <<"2b", a0, m[2], m[3]>> \in msgs'
          BY <3>5
        <4>5. <<"2b", a0, m[2], m[3]>>[1] = "2b" /\ <<"2b", a0, m[2], m[3]>>[2] = a0
          OBVIOUS
        <4>6. <<m[2], m[3]>> \in votes'[a0]
          <5>1. votes'[a0] = {<<mm[3], mm[4]>> : mm \in {mmm \in msgs': /\ mmm[1] = "2b"
                                                                        /\ mmm[2] = a0}}
            BY DEF votes
          <5> QED BY <4>4, <4>5, <5>1
        <4>7. <<maxVBal'[a], maxVal'[a]>> \in votes'[a]
          BY <3>7, <4>1, <4>2, <4>6
        <4> QED BY <4>3, <4>7
      <3>8. CASE a # a0
        <4>1. maxVBal'[a] = maxVBal[a]
          BY <3>1, <3>8
        <4>2. maxVal'[a] = maxVal[a]
          BY <3>1, <3>8
        <4>3. \A mm \in msgs : (mm[1] = "2b" /\ mm[2] = a) =>
                                  mm \in msgs' /\ mm[1] = "2b" /\ mm[2] = a
          BY <3>5
        <4>4. \A mm \in msgs' : (mm[1] = "2b" /\ mm[2] = a) =>
                                   mm \in msgs /\ mm[1] = "2b" /\ mm[2] = a
          BY <3>5, <3>8
        <4>5. votes'[a] = votes[a]
          BY <4>3, <4>4 DEF votes
        <4>6. CASE maxVBal[a] = -1
          <5>1. maxVBal'[a] = -1
            BY <4>1, <4>6
          <5>2. maxVal[a] = None
            BY <4>6 DEF StructOK1
          <5>3. maxVal'[a] = None
            BY <4>2, <5>2
          <5> QED BY <5>1, <5>3
        <4>7. CASE maxVBal[a] # -1
          <5>1. maxVBal'[a] # -1
            BY <4>1, <4>7
          <5>2. <<maxVBal[a], maxVal[a]>> \in votes[a]
            BY <4>7 DEF StructOK1
          <5>3. <<maxVBal'[a], maxVal'[a]>> \in votes'[a]
            BY <4>1, <4>2, <4>5, <5>2
          <5> QED BY <5>1, <5>3
        <4> QED BY <4>6, <4>7
      <3> QED BY <3>7, <3>8
    <2> QED BY <2>1, <2>2, <2>3, <2>4
  <1> QED BY <1>1, <1>2

LEMMA NextInv == IndInv /\ [Next]_vars => IndInv'
  BY TypeOKInv, StructOK1Inv DEF IndInv

THEOREM Spec => []StructOK1
  <1>1. Spec => []IndInv
    <2>1. Init => IndInv
      BY InitInv
    <2>2. IndInv /\ [Next]_vars => IndInv'
      BY NextInv
    <2> QED BY <2>1, <2>2, PTL DEF Spec
  <1>2. IndInv => StructOK1
    BY DEF IndInv
  <1> QED BY <1>1, <1>2, PTL
-----------------------------------------------------------

-----------------------------------------------------------------------------

------------------------------------------------------------
============================================================
