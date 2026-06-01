------------------------------- MODULE Paxos_Refinement -------------------------------

EXTENDS Integers, TLAPS, TLC
-----------------------------------------------------------------------------
CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == Nat

None == CHOOSE v : v \notin Values

-----------------------------------------------------------------------------
VARIABLES msgs,
          maxBal,
          maxVBal,
          maxVal

vars == <<msgs, maxBal, maxVBal, maxVal>>

Send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]

Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
              /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxVBal, maxBal, maxVal>>

Phase1b(a) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.bal > maxBal[a]
     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
     /\ Send([type |-> "1b", bal |-> m.bal,
           maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a])
     /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b) ==
  /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
  /\ \E v \in Values :
       /\ \E Q \in Quorums :
            \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) :
                        /\ \A m \in S : m.maxVBal =< c
                        /\ \E m \in S : /\ m.maxVBal = c
                                        /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
-----------------------------------------------------------------------------
Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
chosenBar == {v \in Values : Chosen(v)}

C == INSTANCE Consensus WITH chosen <- chosenBar

\* ==========================================================================
\* Helper definitions and inductive invariant
\* ==========================================================================

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
        maxVal : Values \cup {None}, acc : Acceptors]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK ==
  /\ msgs \subseteq Messages
  /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVal \in [Acceptors -> Values \cup {None}]
  /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]

WontVoteIn(a, b) ==
  /\ \A v \in Values : ~ VotedForIn(a, v, b)
  /\ maxBal[a] > b

SafeAt(v, b) ==
  \A c \in 0..(b-1) :
    \E Q \in Quorums :
      \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)

MsgInv ==
  \A m \in msgs :
    /\ (m.type = "1b") =>
         /\ m.bal =< maxBal[m.acc]
         /\ \/ (m.maxVBal = -1 /\ m.maxVal = None)
            \/ /\ m.maxVBal \in 0..(m.bal-1)
               /\ m.maxVal \in Values
               /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
         /\ \A c \in (m.maxVBal+1)..(m.bal-1) :
              ~ \E v \in Values : VotedForIn(m.acc, v, c)
    /\ (m.type = "2a") =>
         /\ SafeAt(m.val, m.bal)
         /\ \A mm \in msgs :
              (mm.type = "2a") /\ (mm.bal = m.bal) => mm.val = m.val
    /\ (m.type = "2b") =>
         /\ \E mm \in msgs : /\ mm.type = "2a"
                             /\ mm.bal = m.bal
                             /\ mm.val = m.val
         /\ m.bal =< maxVBal[m.acc]

AccInv ==
  \A a \in Acceptors :
    /\ (maxVBal[a] = -1) <=> (maxVal[a] = None)
    /\ (maxVal[a] # None) =>
         /\ maxVal[a] \in Values
         /\ maxVBal[a] \in Ballots
         /\ VotedForIn(a, maxVal[a], maxVBal[a])
    /\ \A c \in Ballots : c > maxVBal[a] =>
         ~ \E v \in Values : VotedForIn(a, v, c)

IndInv == TypeOK /\ MsgInv /\ AccInv

-----------------------------------------------------------------------------
\* Basic lemmas about VotedForIn

LEMMA VotedForInv ==
  ASSUME TypeOK, NEW a \in Acceptors, NEW v, NEW b, VotedForIn(a, v, b)
  PROVE  v \in Values /\ b \in Ballots
<1>1. PICK m \in msgs : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a
      BY DEF VotedForIn
<1>2. m \in Messages BY DEF TypeOK
<1>. QED BY <1>1, <1>2 DEF Messages

LEMMA VotedInv ==
  ASSUME IndInv, NEW a \in Acceptors, NEW v, NEW b, VotedForIn(a, v, b)
  PROVE  /\ b \in Ballots
         /\ v \in Values
         /\ \E mm \in msgs : /\ mm.type = "2a" /\ mm.bal = b /\ mm.val = v
<1>1. PICK m \in msgs : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a
      BY DEF VotedForIn
<1>2. m \in Messages BY DEF IndInv, TypeOK
<1>3. v \in Values /\ b \in Ballots BY <1>1, <1>2 DEF Messages
<1>4. \E mm \in msgs : /\ mm.type = "2a" /\ mm.bal = b /\ mm.val = v
      BY <1>1 DEF IndInv, MsgInv
<1>. QED BY <1>3, <1>4

LEMMA VotedOnce ==
  ASSUME IndInv,
         NEW a1 \in Acceptors, NEW a2 \in Acceptors,
         NEW v1, NEW v2, NEW b,
         VotedForIn(a1, v1, b), VotedForIn(a2, v2, b)
  PROVE  v1 = v2
<1>1. PICK mm1 \in msgs : /\ mm1.type = "2a" /\ mm1.bal = b /\ mm1.val = v1
      BY VotedInv DEF IndInv
<1>2. PICK mm2 \in msgs : /\ mm2.type = "2a" /\ mm2.bal = b /\ mm2.val = v2
      BY VotedInv DEF IndInv
<1>. QED BY <1>1, <1>2 DEF IndInv, MsgInv

LEMMA ChosenIsValue ==
  ASSUME IndInv, NEW v, Chosen(v)
  PROVE  v \in Values
<1>1. PICK b \in Ballots : ChosenIn(v, b) BY DEF Chosen
<1>2. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)
      BY <1>1 DEF ChosenIn
<1>3. Q # {}
      <2>1. PICK Q2 \in Quorums : TRUE BY QuorumAssumption
      <2>2. Q \cap Q2 # {} BY <2>1, QuorumAssumption
      <2>. QED BY <2>2
<1>4. PICK a \in Q : VotedForIn(a, v, b) BY <1>2, <1>3
<1>5. a \in Acceptors BY <1>4, QuorumAssumption
<1>. QED BY VotedForInv, <1>4, <1>5 DEF IndInv

-----------------------------------------------------------------------------
\* Initial state lemma

LEMMA InitInv == Init => IndInv
<1>1. SUFFICES ASSUME Init PROVE IndInv OBVIOUS
<1>2. TypeOK
  <2>1. msgs \subseteq Messages BY <1>1 DEF Init
  <2>2. maxVBal \in [Acceptors -> Ballots \cup {-1}] BY <1>1 DEF Init
  <2>3. maxBal \in [Acceptors -> Ballots \cup {-1}] BY <1>1 DEF Init
  <2>4. maxVal \in [Acceptors -> Values \cup {None}] BY <1>1 DEF Init
  <2>5. \A a \in Acceptors : maxBal[a] >= maxVBal[a] BY <1>1 DEF Init
  <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
<1>3. MsgInv BY <1>1 DEF Init, MsgInv
<1>4. AccInv
  <2>1. \A a \in Acceptors : (maxVBal[a] = -1) <=> (maxVal[a] = None)
        BY <1>1 DEF Init
  <2>2. \A a \in Acceptors : (maxVal[a] # None) =>
            /\ maxVal[a] \in Values
            /\ maxVBal[a] \in Ballots
            /\ VotedForIn(a, maxVal[a], maxVBal[a])
        BY <1>1 DEF Init
  <2>3. \A a \in Acceptors : \A c \in Ballots : c > maxVBal[a] =>
            ~ \E v \in Values : VotedForIn(a, v, c)
    <3>1. \A a \in Acceptors : \A c, v : ~ VotedForIn(a, v, c)
          BY <1>1 DEF Init, VotedForIn
    <3>. QED BY <3>1
  <2>. QED BY <2>1, <2>2, <2>3 DEF AccInv
<1>. QED BY <1>2, <1>3, <1>4 DEF IndInv

-----------------------------------------------------------------------------
\* VotedForIn and WontVoteIn preservation lemmas

LEMMA VotedForInMono ==
  ASSUME NEW a, NEW v, NEW b, VotedForIn(a, v, b), msgs \subseteq msgs'
  PROVE  VotedForIn(a, v, b)'
BY DEF VotedForIn

-----------------------------------------------------------------------------
\* Phase1a preserves the invariant

LEMMA Phase1aInv ==
  ASSUME IndInv, NEW bbb \in Ballots, Phase1a(bbb)
  PROVE  IndInv'
<1>1. msgs' = msgs \cup {[type |-> "1a", bal |-> bbb]}
      BY DEF Phase1a, Send
<1>2. maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
      BY DEF Phase1a
<1>m. msgs \subseteq msgs'
      BY <1>1
<1>3. TypeOK'
      BY <1>1, <1>2 DEF IndInv, TypeOK, Messages
<1>4. AccInv'
      BY <1>1, <1>2 DEF IndInv, AccInv, VotedForIn
<1>5. MsgInv'
      BY <1>1, <1>2 DEF IndInv, TypeOK, Messages, MsgInv, SafeAt, WontVoteIn, VotedForIn
<1>. QED BY <1>3, <1>4, <1>5 DEF IndInv

-----------------------------------------------------------------------------
\* Phase1b preserves the invariant

LEMMA Phase1bInv ==
  ASSUME IndInv, NEW a \in Acceptors, Phase1b(a)
  PROVE  IndInv'
<1>0. PICK m \in msgs :
            /\ m.type = "1a"
            /\ m.bal > maxBal[a]
            /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
            /\ Send([type |-> "1b", bal |-> m.bal,
                  maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a])
            /\ UNCHANGED <<maxVBal, maxVal>>
      BY DEF Phase1b
<1>0a. m \in Messages
       BY <1>0 DEF IndInv, TypeOK
<1>0b. m.bal \in Ballots
       BY <1>0, <1>0a DEF Messages
<1>1. msgs' = msgs \cup {[type |-> "1b", bal |-> m.bal,
              maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a]}
      BY <1>0 DEF Send
<1>m. msgs \subseteq msgs' BY <1>1
<1>2. /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
      /\ maxVBal' = maxVBal
      /\ maxVal' = maxVal
      BY <1>0
<1>2a. \A x \in Acceptors : maxBal'[x] >= maxBal[x] /\ maxBal'[x] \in Ballots \cup {-1}
  <2>1. SUFFICES ASSUME NEW x \in Acceptors
                 PROVE maxBal'[x] >= maxBal[x] /\ maxBal'[x] \in Ballots \cup {-1}
        OBVIOUS
  <2>2. maxBal \in [Acceptors -> Ballots \cup {-1}] BY DEF IndInv, TypeOK
  <2>3. CASE x = a
        <3>1. maxBal'[a] = m.bal BY <1>2, <2>2
        <3>2. m.bal > maxBal[a] BY <1>0
        <3>3. maxBal[a] \in Ballots \cup {-1} BY <2>2
        <3>4. m.bal >= maxBal[a]
              <4>. QED BY <3>2, <3>3, <1>0b DEF Ballots
        <3>. QED BY <3>1, <3>4, <1>0b, <2>3 DEF Ballots
  <2>4. CASE x # a
        <3>1. maxBal'[x] = maxBal[x] BY <1>2, <2>2, <2>4
        <3>2. maxBal[x] \in Ballots \cup {-1} BY <2>2
        <3>3. maxBal[x] >= maxBal[x] BY <3>2 DEF Ballots
        <3>. QED BY <3>1, <3>2, <3>3
  <2>. QED BY <2>3, <2>4
<1>2b. maxBal' = [x \in Acceptors |-> IF x = a THEN m.bal ELSE maxBal[x]]
  <2>1. maxBal \in [Acceptors -> Ballots \cup {-1}] BY DEF IndInv, TypeOK
  <2>. QED BY <2>1, <1>2
<1>3. TypeOK'
  <2>1. msgs' \subseteq Messages
        BY <1>1, <1>0b DEF IndInv, TypeOK, Messages
  <2>2. maxBal' \in [Acceptors -> Ballots \cup {-1}]
    <3>1. \A x \in Acceptors : maxBal'[x] \in Ballots \cup {-1} BY <1>2a
    <3>. QED BY <3>1, <1>2b
  <2>3. maxVBal' \in [Acceptors -> Ballots \cup {-1}]
        BY <1>2 DEF IndInv, TypeOK
  <2>4. maxVal' \in [Acceptors -> Values \cup {None}]
        BY <1>2 DEF IndInv, TypeOK
  <2>5. \A x \in Acceptors : maxBal'[x] >= maxVBal'[x]
    <3>1. SUFFICES ASSUME NEW x \in Acceptors PROVE maxBal'[x] >= maxVBal'[x]
          OBVIOUS
    <3>2. maxBal'[x] >= maxBal[x] /\ maxBal'[x] \in Ballots \cup {-1} BY <1>2a
    <3>3. maxBal[x] >= maxVBal[x] BY DEF IndInv, TypeOK
    <3>4. maxVBal'[x] = maxVBal[x] BY <1>2
    <3>5. maxBal[x] \in Ballots \cup {-1}
          /\ maxVBal[x] \in Ballots \cup {-1}
          BY DEF IndInv, TypeOK
    <3>. QED BY <3>2, <3>3, <3>4, <3>5 DEF Ballots
  <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
<1>4. AccInv'
      BY <1>1, <1>2, <1>0b DEF IndInv, AccInv, TypeOK, VotedForIn
<1>5. MsgInv'
      BY <1>1, <1>2, <1>2a, <1>0, <1>0b, QuorumAssumption
         DEF IndInv, TypeOK, Messages, MsgInv, AccInv, SafeAt, WontVoteIn, VotedForIn, Ballots
<1>. QED BY <1>3, <1>4, <1>5 DEF IndInv

-----------------------------------------------------------------------------
\* Phase2b preserves the invariant

LEMMA Phase2bInv ==
  ASSUME IndInv, NEW a \in Acceptors, Phase2b(a)
  PROVE  IndInv'
<1>0. PICK m \in msgs :
            /\ m.type = "2a"
            /\ m.bal >= maxBal[a]
            /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
            /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
            /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
            /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
      BY DEF Phase2b
<1>0a. m \in Messages BY <1>0 DEF IndInv, TypeOK
<1>0b. m.bal \in Ballots /\ m.val \in Values BY <1>0, <1>0a DEF Messages
<1>0c. SafeAt(m.val, m.bal) BY <1>0 DEF IndInv, MsgInv
<1>0d. \A m2 \in msgs : (m2.type = "2a") /\ (m2.bal = m.bal) => m2.val = m.val
       BY <1>0 DEF IndInv, MsgInv
<1>1. msgs' = msgs \cup {[type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]}
      BY <1>0 DEF Send
<1>m. msgs \subseteq msgs' BY <1>1
<1>2. /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
      /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
      /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
      BY <1>0
<1>2a. \A x \in Acceptors : maxBal'[x] >= maxBal[x] /\ maxBal'[x] \in Ballots \cup {-1}
  <2>1. SUFFICES ASSUME NEW x \in Acceptors
                 PROVE maxBal'[x] >= maxBal[x] /\ maxBal'[x] \in Ballots \cup {-1}
        OBVIOUS
  <2>2. maxBal \in [Acceptors -> Ballots \cup {-1}] BY DEF IndInv, TypeOK
  <2>3. CASE x = a
        <3>1. maxBal'[a] = m.bal BY <1>2, <2>2
        <3>2. m.bal >= maxBal[a] BY <1>0
        <3>3. maxBal[a] \in Ballots \cup {-1} BY <2>2
        <3>. QED BY <3>1, <3>2, <3>3, <1>0b, <2>3 DEF Ballots
  <2>4. CASE x # a
        <3>1. maxBal'[x] = maxBal[x] BY <1>2, <2>2, <2>4
        <3>2. maxBal[x] \in Ballots \cup {-1} BY <2>2
        <3>3. maxBal[x] >= maxBal[x] BY <3>2 DEF Ballots
        <3>. QED BY <3>1, <3>2, <3>3
  <2>. QED BY <2>3, <2>4
<1>2b. \A x \in Acceptors : maxVBal'[x] >= maxVBal[x] /\ maxVBal'[x] \in Ballots \cup {-1}
  <2>1. SUFFICES ASSUME NEW x \in Acceptors
                 PROVE maxVBal'[x] >= maxVBal[x] /\ maxVBal'[x] \in Ballots \cup {-1}
        OBVIOUS
  <2>2. maxVBal \in [Acceptors -> Ballots \cup {-1}] BY DEF IndInv, TypeOK
  <2>3. CASE x = a
        <3>1. maxVBal'[a] = m.bal BY <1>2, <2>2
        <3>2. m.bal >= maxBal[a] BY <1>0
        <3>3. maxBal[a] >= maxVBal[a] BY DEF IndInv, TypeOK
        <3>4. maxVBal[a] \in Ballots \cup {-1} BY <2>2
        <3>5. m.bal >= maxVBal[a] BY <3>2, <3>3, <3>4, <1>0b DEF IndInv, TypeOK, Ballots
        <3>. QED BY <3>1, <3>5, <1>0b, <2>3 DEF Ballots
  <2>4. CASE x # a
        <3>1. maxVBal'[x] = maxVBal[x] BY <1>2, <2>2, <2>4
        <3>2. maxVBal[x] \in Ballots \cup {-1} BY <2>2
        <3>3. maxVBal[x] >= maxVBal[x] BY <3>2 DEF Ballots
        <3>. QED BY <3>1, <3>2, <3>3
  <2>. QED BY <2>3, <2>4
<1>2c. maxBal' = [x \in Acceptors |-> IF x = a THEN m.bal ELSE maxBal[x]]
       /\ maxVBal' = [x \in Acceptors |-> IF x = a THEN m.bal ELSE maxVBal[x]]
       /\ maxVal' = [x \in Acceptors |-> IF x = a THEN m.val ELSE maxVal[x]]
  <2>1. /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
        /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
        /\ maxVal \in [Acceptors -> Values \cup {None}]
        BY DEF IndInv, TypeOK
  <2>. QED BY <2>1, <1>2
<1>3. TypeOK'
  <2>1. msgs' \subseteq Messages
        BY <1>1, <1>0b DEF IndInv, TypeOK, Messages
  <2>2. maxBal' \in [Acceptors -> Ballots \cup {-1}]
    <3>1. \A x \in Acceptors : maxBal'[x] \in Ballots \cup {-1} BY <1>2a
    <3>. QED BY <3>1, <1>2c
  <2>3. maxVBal' \in [Acceptors -> Ballots \cup {-1}]
    <3>1. \A x \in Acceptors : maxVBal'[x] \in Ballots \cup {-1} BY <1>2b
    <3>. QED BY <3>1, <1>2c
  <2>4. maxVal' \in [Acceptors -> Values \cup {None}]
    <3>1. SUFFICES \A x \in Acceptors : maxVal'[x] \in Values \cup {None} BY <1>2c
    <3>2. maxVal \in [Acceptors -> Values \cup {None}] BY DEF IndInv, TypeOK
    <3>. QED BY <3>2, <1>2c, <1>0b
  <2>5. \A x \in Acceptors : maxBal'[x] >= maxVBal'[x]
    <3>1. SUFFICES ASSUME NEW x \in Acceptors PROVE maxBal'[x] >= maxVBal'[x]
          OBVIOUS
    <3>2. CASE x = a
          <4>1. maxBal'[a] = m.bal /\ maxVBal'[a] = m.bal BY <1>2c
          <4>. QED BY <4>1, <1>0b, <3>2 DEF Ballots
    <3>3. CASE x # a
          <4>1. maxBal'[x] = maxBal[x] /\ maxVBal'[x] = maxVBal[x] BY <1>2c, <3>3
          <4>2. maxBal[x] >= maxVBal[x] BY DEF IndInv, TypeOK
          <4>. QED BY <4>1, <4>2
    <3>. QED BY <3>2, <3>3
  <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
<1>VFI2. ASSUME NEW x \in Acceptors, NEW v, NEW b, VotedForIn(x, v, b)'
         PROVE  VotedForIn(x, v, b) \/ (x = a /\ v = m.val /\ b = m.bal)
  <2>1. PICK m2 \in msgs' : m2.type = "2b" /\ m2.val = v /\ m2.bal = b /\ m2.acc = x
        BY <1>VFI2 DEF VotedForIn
  <2>2. CASE m2 \in msgs
        BY <2>1, <2>2 DEF VotedForIn
  <2>3. CASE m2 \notin msgs
        <3>1. m2 = [type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]
              BY <1>1, <2>3
        <3>. QED BY <3>1, <2>1
  <2>. QED BY <2>2, <2>3
<1>4. AccInv'
  <2>0. SUFFICES ASSUME NEW x \in Acceptors
                 PROVE  /\ (maxVBal'[x] = -1) <=> (maxVal'[x] = None)
                        /\ (maxVal'[x] # None) =>
                             /\ maxVal'[x] \in Values
                             /\ maxVBal'[x] \in Ballots
                             /\ \E mm \in msgs' : /\ mm.type = "2b"
                                                  /\ mm.val = maxVal'[x]
                                                  /\ mm.bal = maxVBal'[x]
                                                  /\ mm.acc = x
                        /\ \A c \in Ballots : c > maxVBal'[x] =>
                             ~ \E v \in Values :
                                  \E mm \in msgs' : /\ mm.type = "2b"
                                                    /\ mm.val = v
                                                    /\ mm.bal = c
                                                    /\ mm.acc = x
        BY DEF AccInv, VotedForIn
  <2>1. CASE x = a
    <3>1. maxBal'[a] = m.bal /\ maxVBal'[a] = m.bal /\ maxVal'[a] = m.val
          BY <1>2c
    <3>2. m.bal \in Nat /\ m.val \in Values BY <1>0b DEF Ballots
    <3>3. (maxVBal'[x] = -1) <=> (maxVal'[x] = None)
      <4>1. None \notin Values BY NoSetContainsEverything DEF None
      <4>. QED BY <3>1, <3>2, <2>1, <4>1
    <3>4. ASSUME maxVal'[x] # None
          PROVE /\ maxVal'[x] \in Values
                /\ maxVBal'[x] \in Ballots
                /\ \E mm \in msgs' : /\ mm.type = "2b"
                                     /\ mm.val = maxVal'[x]
                                     /\ mm.bal = maxVBal'[x]
                                     /\ mm.acc = x
      <4>1. maxVal'[x] = m.val /\ maxVBal'[x] = m.bal BY <3>1, <2>1
      <4>2. [type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a] \in msgs'
            BY <1>1
      <4>3. maxVal'[x] \in Values /\ maxVBal'[x] \in Ballots BY <4>1, <3>2 DEF Ballots
      <4>4. \E mm \in msgs' : /\ mm.type = "2b"
                              /\ mm.val = maxVal'[x]
                              /\ mm.bal = maxVBal'[x]
                              /\ mm.acc = x
        <5>1. LET mm == [type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]
              IN /\ mm \in msgs'
                 /\ mm.type = "2b"
                 /\ mm.val = maxVal'[x]
                 /\ mm.bal = maxVBal'[x]
                 /\ mm.acc = x
              BY <4>1, <4>2, <2>1
        <5>. QED BY <5>1
      <4>. QED BY <4>3, <4>4
    <3>5. \A c \in Ballots : c > maxVBal'[x] =>
                 ~ \E v \in Values :
                      \E mm \in msgs' : /\ mm.type = "2b"
                                        /\ mm.val = v
                                        /\ mm.bal = c
                                        /\ mm.acc = x
      <4>1. SUFFICES ASSUME NEW c \in Ballots, c > maxVBal'[x],
                            NEW v \in Values,
                            NEW m2 \in msgs',
                            m2.type = "2b" /\ m2.val = v /\ m2.bal = c /\ m2.acc = x
                     PROVE FALSE
            OBVIOUS
      <4>2. c > m.bal BY <4>1, <3>1, <2>1
      <4>3. VotedForIn(x, v, c)' BY <4>1 DEF VotedForIn
      <4>4. VotedForIn(x, v, c) \/ (x = a /\ v = m.val /\ c = m.bal)
            BY <1>VFI2, <4>3
      <4>5. CASE VotedForIn(x, v, c)
        <5>2. m.bal >= maxBal[a] BY <1>0
        <5>3. maxBal[a] >= maxVBal[a] BY DEF IndInv, TypeOK
        <5>4. maxBal[a] \in Ballots \cup {-1} /\ maxVBal[a] \in Ballots \cup {-1}
              BY DEF IndInv, TypeOK
        <5>5. c > maxVBal[a]
              BY <4>2, <5>2, <5>3, <5>4, <1>0b, <4>1 DEF Ballots
        <5>. QED BY <5>5, <4>5, <2>1, <4>1 DEF IndInv, AccInv
      <4>6. CASE x = a /\ v = m.val /\ c = m.bal
            BY <4>6, <4>2
      <4>. QED BY <4>4, <4>5, <4>6
    <3>. QED BY <3>3, <3>4, <3>5
  <2>2. CASE x # a
    <3>1. maxBal'[x] = maxBal[x] /\ maxVBal'[x] = maxVBal[x] /\ maxVal'[x] = maxVal[x]
          BY <1>2c, <2>2
    <3>2. (maxVBal'[x] = -1) <=> (maxVal'[x] = None)
          BY <3>1 DEF IndInv, AccInv
    <3>3. ASSUME maxVal'[x] # None
          PROVE /\ maxVal'[x] \in Values
                /\ maxVBal'[x] \in Ballots
                /\ \E mm \in msgs' : /\ mm.type = "2b"
                                     /\ mm.val = maxVal'[x]
                                     /\ mm.bal = maxVBal'[x]
                                     /\ mm.acc = x
      <4>1. maxVal[x] # None BY <3>3, <3>1
      <4>2. /\ maxVal[x] \in Values
            /\ maxVBal[x] \in Ballots
            /\ VotedForIn(x, maxVal[x], maxVBal[x])
            BY <4>1 DEF IndInv, AccInv
      <4>3. PICK mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[x] /\ mm.bal = maxVBal[x] /\ mm.acc = x
            BY <4>2 DEF VotedForIn
      <4>4. mm \in msgs' BY <4>3, <1>m
      <4>. QED BY <3>1, <4>2, <4>3, <4>4
    <3>4. \A c \in Ballots : c > maxVBal'[x] =>
                 ~ \E v \in Values :
                      \E mm \in msgs' : /\ mm.type = "2b"
                                        /\ mm.val = v
                                        /\ mm.bal = c
                                        /\ mm.acc = x
      <4>1. SUFFICES ASSUME NEW c \in Ballots, c > maxVBal'[x],
                            NEW v \in Values,
                            NEW m2 \in msgs',
                            m2.type = "2b" /\ m2.val = v /\ m2.bal = c /\ m2.acc = x
                     PROVE FALSE
            OBVIOUS
      <4>2. c > maxVBal[x] BY <4>1, <3>1
      <4>3. VotedForIn(x, v, c)' BY <4>1 DEF VotedForIn
      <4>4. VotedForIn(x, v, c) \/ (x = a /\ v = m.val /\ c = m.bal)
            BY <1>VFI2, <4>3
      <4>5. CASE VotedForIn(x, v, c)
            BY <4>5, <4>2 DEF IndInv, AccInv
      <4>6. CASE x = a /\ v = m.val /\ c = m.bal
            BY <4>6, <2>2
      <4>. QED BY <4>4, <4>5, <4>6
    <3>. QED BY <3>2, <3>3, <3>4
  <2>. QED BY <2>1, <2>2
<1>5. MsgInv'
  <2>1. SUFFICES ASSUME NEW mm \in msgs' PROVE
          /\ (mm.type = "1b") =>
               /\ mm.bal =< maxBal'[mm.acc]
               /\ \/ (mm.maxVBal = -1 /\ mm.maxVal = None)
                  \/ /\ mm.maxVBal \in 0..(mm.bal-1)
                     /\ mm.maxVal \in Values
                     /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
               /\ \A c \in (mm.maxVBal+1)..(mm.bal-1) :
                    ~ \E v \in Values : VotedForIn(mm.acc, v, c)'
          /\ (mm.type = "2a") =>
               /\ SafeAt(mm.val, mm.bal)'
               /\ \A m2 \in msgs' :
                    (m2.type = "2a") /\ (m2.bal = mm.bal) => m2.val = mm.val
          /\ (mm.type = "2b") =>
               /\ \E m2 \in msgs' : /\ m2.type = "2a"
                                    /\ m2.bal = mm.bal
                                    /\ m2.val = mm.val
               /\ mm.bal =< maxVBal'[mm.acc]
        BY DEF MsgInv
  <2>SA. ASSUME NEW v, NEW b, SafeAt(v, b)
         PROVE  SafeAt(v, b)'
    <3>0. SafeAt(v, b) BY <2>SA
    <3>1. SUFFICES ASSUME NEW c \in 0..(b-1)
                   PROVE \E Q \in Quorums :
                           \A x \in Q : VotedForIn(x, v, c)' \/ WontVoteIn(x, c)'
          BY DEF SafeAt
    <3>2. PICK Q \in Quorums : \A x \in Q : VotedForIn(x, v, c) \/ WontVoteIn(x, c)
          BY <3>0, <3>1 DEF SafeAt
    <3>3. Q \subseteq Acceptors BY QuorumAssumption
    <3>4. \A x \in Q : VotedForIn(x, v, c)' \/ WontVoteIn(x, c)'
      <4>1. SUFFICES ASSUME NEW x \in Q
                     PROVE VotedForIn(x, v, c)' \/ WontVoteIn(x, c)'
            OBVIOUS
      <4>2. x \in Acceptors BY <3>3, <4>1
      <4>3. CASE VotedForIn(x, v, c)
            BY <4>3, <1>m DEF VotedForIn
      <4>4. CASE WontVoteIn(x, c)
        <5>1. \A vv \in Values : ~ VotedForIn(x, vv, c) BY <4>4 DEF WontVoteIn
        <5>2. maxBal[x] > c BY <4>4 DEF WontVoteIn
        <5>3. maxBal'[x] >= maxBal[x] BY <1>2a, <4>2
        <5>4. maxBal'[x] > c
          <6>1. maxBal[x] \in Ballots \cup {-1} BY <4>2 DEF IndInv, TypeOK
          <6>2. maxBal'[x] \in Ballots \cup {-1} BY <1>2a, <4>2
          <6>. QED BY <5>2, <5>3, <6>1, <6>2 DEF Ballots
        <5>5. \A vv \in Values : ~ VotedForIn(x, vv, c)'
          <6>1. SUFFICES ASSUME NEW vv \in Values, VotedForIn(x, vv, c)'
                         PROVE FALSE
                OBVIOUS
          <6>2. VotedForIn(x, vv, c) \/ (x = a /\ vv = m.val /\ c = m.bal)
                BY <1>VFI2, <4>2, <6>1
          <6>3. CASE VotedForIn(x, vv, c)
                BY <6>3, <5>1, <6>1
          <6>4. CASE x = a /\ vv = m.val /\ c = m.bal
            <7>1. c = m.bal BY <6>4
            <7>2. maxBal[a] =< m.bal BY <1>0
            <7>3. ~ (maxBal[a] > m.bal) BY <7>2, <1>0b DEF IndInv, TypeOK, Ballots
            <7>4. c = m.bal /\ x = a BY <6>4
            <7>5. maxBal[x] > c BY <5>2
            <7>. QED BY <7>1, <7>3, <7>4, <7>5
          <6>. QED BY <6>2, <6>3, <6>4
        <5>. QED BY <5>4, <5>5 DEF WontVoteIn
      <4>. QED BY <4>3, <4>4, <3>2, <4>1
    <3>. QED BY <3>4
  <2>2. CASE mm \notin msgs
    <3>1. mm = [type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]
          BY <1>1, <2>2
    <3>2. mm.type = "2b" /\ mm.acc = a /\ mm.bal = m.bal /\ mm.val = m.val
          BY <3>1
    <3>3. \E m2 \in msgs' : m2.type = "2a" /\ m2.bal = mm.bal /\ m2.val = mm.val
      <4>1. m \in msgs' BY <1>m, <1>0
      <4>. QED BY <4>1, <1>0, <3>2
    <3>4. mm.bal =< maxVBal'[mm.acc]
      <4>1. maxVBal'[a] = m.bal BY <1>2c
      <4>. QED BY <4>1, <3>2, <1>0b DEF Ballots
    <3>. QED BY <3>2, <3>3, <3>4
  <2>3. CASE mm \in msgs
    <3>0. mm \in Messages BY <2>3 DEF IndInv, TypeOK
    <3>1. CASE mm.type = "1b"
      <4>1. mm.acc \in Acceptors BY <3>0, <3>1 DEF Messages
      <4>2. /\ mm.bal =< maxBal[mm.acc]
            /\ \/ (mm.maxVBal = -1 /\ mm.maxVal = None)
               \/ /\ mm.maxVBal \in 0..(mm.bal-1)
                  /\ mm.maxVal \in Values
                  /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
            /\ \A c \in (mm.maxVBal+1)..(mm.bal-1) :
                 ~ \E v \in Values : VotedForIn(mm.acc, v, c)
            BY <3>1, <2>3 DEF IndInv, MsgInv
      <4>3. mm.bal =< maxBal'[mm.acc]
            <5>1. maxBal'[mm.acc] >= maxBal[mm.acc] BY <1>2a, <4>1
            <5>2. mm.bal \in Ballots BY <3>0, <3>1 DEF Messages
            <5>3. maxBal[mm.acc] \in Ballots \cup {-1} BY <4>1 DEF IndInv, TypeOK
            <5>4. maxBal'[mm.acc] \in Ballots \cup {-1} BY <1>2a, <4>1
            <5>. QED BY <4>2, <5>1, <5>2, <5>3, <5>4 DEF Ballots
      <4>4. \/ (mm.maxVBal = -1 /\ mm.maxVal = None)
            \/ /\ mm.maxVBal \in 0..(mm.bal-1)
               /\ mm.maxVal \in Values
               /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
            BY <4>2, <1>m DEF VotedForIn
      <4>5. \A c \in (mm.maxVBal+1)..(mm.bal-1) :
                 ~ \E v \in Values : VotedForIn(mm.acc, v, c)'
        <5>1. SUFFICES ASSUME NEW c \in (mm.maxVBal+1)..(mm.bal-1),
                              NEW v \in Values, VotedForIn(mm.acc, v, c)'
                       PROVE FALSE
              OBVIOUS
        <5>2. VotedForIn(mm.acc, v, c) \/ (mm.acc = a /\ v = m.val /\ c = m.bal)
              BY <1>VFI2, <4>1, <5>1
        <5>3. CASE VotedForIn(mm.acc, v, c)
              BY <4>2, <5>1, <5>3
        <5>4. CASE mm.acc = a /\ v = m.val /\ c = m.bal
          <6>1. c = m.bal BY <5>4
          <6>2. mm.bal \in Ballots BY <3>0, <3>1 DEF Messages
          <6>3. c \in (mm.maxVBal+1)..(mm.bal-1) BY <5>1
          <6>4. mm.bal \in Nat BY <6>2 DEF Ballots
          <6>4b. c < mm.bal BY <6>3, <6>4
          <6>5. mm.bal =< maxBal[mm.acc] BY <4>2
          <6>6. maxBal[mm.acc] = maxBal[a] BY <5>4
          <6>7. mm.bal =< maxBal[a] BY <6>5, <6>6
          <6>8. m.bal >= maxBal[a] BY <1>0
          <6>9. m.bal < mm.bal BY <6>1, <6>4b
          <6>10. maxBal[a] \in Ballots \cup {-1} BY DEF IndInv, TypeOK
          <6>. QED BY <6>7, <6>8, <6>9, <6>10, <1>0b, <6>2 DEF Ballots
        <5>. QED BY <5>2, <5>3, <5>4
      <4>. QED BY <3>1, <4>3, <4>4, <4>5
    <3>2. CASE mm.type = "2a"
      <4>0. mm.val \in Values /\ mm.bal \in Ballots BY <3>0, <3>2 DEF Messages
      <4>1. SafeAt(mm.val, mm.bal) BY <3>2, <2>3 DEF IndInv, MsgInv
      <4>2. SafeAt(mm.val, mm.bal)' BY <2>SA, <4>1
      <4>3. \A m2 \in msgs' : (m2.type = "2a") /\ (m2.bal = mm.bal) => m2.val = mm.val
        <5>1. SUFFICES ASSUME NEW m2 \in msgs', m2.type = "2a", m2.bal = mm.bal
                       PROVE m2.val = mm.val
              OBVIOUS
        <5>2. m2 \in msgs BY <1>1, <5>1
        <5>. QED BY <2>3, <3>2, <5>1, <5>2 DEF IndInv, MsgInv
      <4>. QED BY <3>2, <4>2, <4>3
    <3>3. CASE mm.type = "2b"
      <4>0. mm.acc \in Acceptors BY <3>0, <3>3 DEF Messages
      <4>1. \E m2 \in msgs : /\ m2.type = "2a"
                             /\ m2.bal = mm.bal
                             /\ m2.val = mm.val
            BY <3>3, <2>3 DEF IndInv, MsgInv
      <4>2. mm.bal =< maxVBal[mm.acc] BY <3>3, <2>3 DEF IndInv, MsgInv
      <4>3. mm.bal =< maxVBal'[mm.acc]
        <5>1. maxVBal'[mm.acc] >= maxVBal[mm.acc] BY <1>2b, <4>0
        <5>2. mm.bal \in Ballots BY <3>0, <3>3 DEF Messages
        <5>3. maxVBal[mm.acc] \in Ballots \cup {-1} BY <4>0 DEF IndInv, TypeOK
        <5>4. maxVBal'[mm.acc] \in Ballots \cup {-1} BY <1>2b, <4>0
        <5>. QED BY <4>2, <5>1, <5>2, <5>3, <5>4 DEF Ballots
      <4>. QED BY <3>3, <4>1, <4>3, <1>1, <1>2
    <3>. QED BY <3>1, <3>2, <3>3, <3>0 DEF Messages
  <2>. QED BY <2>2, <2>3
<1>. QED BY <1>3, <1>4, <1>5 DEF IndInv

-----------------------------------------------------------------------------
\* Phase2a preserves the invariant

LEMMA Phase2aInv ==
  ASSUME IndInv, NEW bbb \in Ballots, Phase2a(bbb)
  PROVE  IndInv'
<1>0a. ~ \E mp \in msgs : (mp.type = "2a") /\ (mp.bal = bbb)
       BY DEF Phase2a
<1>0b. PICK vv \in Values :
            /\ \E Q \in Quorums :
                 \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = bbb)} :
                    /\ \A x \in Q : \E m \in S : m.acc = x
                    /\ \/ \A m \in S : m.maxVBal = -1
                       \/ \E c \in 0..(bbb-1) :
                             /\ \A m \in S : m.maxVBal =< c
                             /\ \E m \in S : /\ m.maxVBal = c
                                             /\ m.maxVal = vv
            /\ Send([type |-> "2a", bal |-> bbb, val |-> vv])
       BY DEF Phase2a
<1>0c. PICK Q1 \in Quorums :
            \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = bbb)} :
                    /\ \A x \in Q1 : \E m \in S : m.acc = x
                    /\ \/ \A m \in S : m.maxVBal = -1
                       \/ \E c \in 0..(bbb-1) :
                             /\ \A m \in S : m.maxVBal =< c
                             /\ \E m \in S : /\ m.maxVBal = c
                                             /\ m.maxVal = vv
       BY <1>0b
<1>0d. PICK S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = bbb)} :
                    /\ \A x \in Q1 : \E m \in S : m.acc = x
                    /\ \/ \A m \in S : m.maxVBal = -1
                       \/ \E c \in 0..(bbb-1) :
                             /\ \A m \in S : m.maxVBal =< c
                             /\ \E m \in S : /\ m.maxVBal = c
                                             /\ m.maxVal = vv
       BY <1>0c
<1>1. msgs' = msgs \cup {[type |-> "2a", bal |-> bbb, val |-> vv]}
      BY <1>0b DEF Send
<1>m. msgs \subseteq msgs' BY <1>1
<1>2. maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
      BY DEF Phase2a
<1>S1. \A m1 \in S : m1.type = "1b" /\ m1.bal = bbb /\ m1 \in msgs /\ m1 \in Messages
       BY <1>0d DEF IndInv, TypeOK
<1>S2. \A m1 \in S : m1.acc \in Acceptors /\ m1.maxVBal \in Ballots \cup {-1} /\ m1.maxVal \in Values \cup {None}
       BY <1>S1 DEF Messages
<1>3. TypeOK'
      BY <1>1, <1>2 DEF IndInv, TypeOK, Messages
<1>4. AccInv'
  <2>1. SUFFICES ASSUME NEW x \in Acceptors
                 PROVE  /\ (maxVBal'[x] = -1) <=> (maxVal'[x] = None)
                        /\ (maxVal'[x] # None) =>
                             /\ maxVal'[x] \in Values
                             /\ maxVBal'[x] \in Ballots
                             /\ \E mm \in msgs' : /\ mm.type = "2b"
                                                  /\ mm.val = maxVal'[x]
                                                  /\ mm.bal = maxVBal'[x]
                                                  /\ mm.acc = x
                        /\ \A c \in Ballots : c > maxVBal'[x] =>
                             ~ \E v \in Values :
                                  \E mm \in msgs' : /\ mm.type = "2b"
                                                    /\ mm.val = v
                                                    /\ mm.bal = c
                                                    /\ mm.acc = x
        BY DEF AccInv, VotedForIn
  <2>2. (maxVBal'[x] = -1) <=> (maxVal'[x] = None)
        BY <1>2 DEF IndInv, AccInv
  <2>3. ASSUME maxVal'[x] # None
        PROVE  /\ maxVal'[x] \in Values
               /\ maxVBal'[x] \in Ballots
               /\ \E mm \in msgs' : /\ mm.type = "2b"
                                    /\ mm.val = maxVal'[x]
                                    /\ mm.bal = maxVBal'[x]
                                    /\ mm.acc = x
    <3>1. maxVal[x] # None BY <2>3, <1>2
    <3>2. /\ maxVal[x] \in Values
          /\ maxVBal[x] \in Ballots
          /\ VotedForIn(x, maxVal[x], maxVBal[x])
          BY <3>1 DEF IndInv, AccInv
    <3>3. PICK mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[x] /\ mm.bal = maxVBal[x] /\ mm.acc = x
          BY <3>2 DEF VotedForIn
    <3>4. mm \in msgs' BY <3>3, <1>m
    <3>. QED BY <3>2, <3>3, <3>4, <1>2
  <2>4. \A c \in Ballots : c > maxVBal'[x] =>
                ~ \E v \in Values :
                     \E mm \in msgs' : /\ mm.type = "2b"
                                       /\ mm.val = v
                                       /\ mm.bal = c
                                       /\ mm.acc = x
    <3>1. SUFFICES ASSUME NEW c \in Ballots, c > maxVBal'[x],
                          NEW v \in Values,
                          NEW m2 \in msgs',
                          m2.type = "2b" /\ m2.val = v /\ m2.bal = c /\ m2.acc = x
                   PROVE FALSE
          OBVIOUS
    <3>2. m2 \in msgs BY <3>1, <1>1
    <3>3. VotedForIn(x, v, c) BY <3>1, <3>2 DEF VotedForIn
    <3>4. c > maxVBal[x] BY <3>1, <1>2
    <3>. QED BY <3>3, <3>4 DEF IndInv, AccInv
  <2>. QED BY <2>2, <2>3, <2>4
\* Now we need to prove MsgInv'.
\* The hard part is showing SafeAt(vv, bbb)' for the new 2a message.
<1>5. SafeAt(vv, bbb)
  <2>1. SUFFICES ASSUME NEW c \in 0..(bbb-1)
                 PROVE \E QQ \in Quorums :
                         \A x \in QQ : VotedForIn(x, vv, c) \/ WontVoteIn(x, c)
        BY DEF SafeAt
  <2>2. CASE \A m1 \in S : m1.maxVBal = -1
    <3>1. \A x \in Q1 : VotedForIn(x, vv, c) \/ WontVoteIn(x, c)
      <4>1. SUFFICES ASSUME NEW x \in Q1
                     PROVE WontVoteIn(x, c)
            OBVIOUS
      <4>2. PICK m1 \in S : m1.acc = x BY <1>0d, <4>1
      <4>3. m1.type = "1b" /\ m1.bal = bbb /\ m1 \in msgs BY <1>S1, <4>2
      <4>4. m1.maxVBal = -1 BY <2>2, <4>2
      <4>5. x \in Acceptors BY <4>2, <1>S2
      <4>6. m1.bal =< maxBal[x] BY <4>2, <4>3 DEF IndInv, MsgInv
      <4>7. maxBal[x] >= bbb BY <4>3, <4>6, <4>2
      <4>7a. bbb > c
            <5>1. bbb \in Nat /\ c \in Nat BY <2>1 DEF Ballots
            <5>. QED BY <2>1, <5>1
      <4>7b. maxBal[x] \in Ballots \cup {-1} BY <4>5 DEF IndInv, TypeOK
      <4>8. maxBal[x] > c
        <5>1. bbb \in Nat /\ c \in Nat BY <2>1 DEF Ballots
        <5>. QED BY <4>7, <4>7a, <5>1, <4>7b DEF Ballots
      <4>9. \A vp \in Values : ~ VotedForIn(x, vp, c)
        <5>1. SUFFICES ASSUME NEW vp \in Values, VotedForIn(x, vp, c)
                       PROVE FALSE
              OBVIOUS
        <5>2. \A c2 \in (m1.maxVBal+1)..(m1.bal-1) : ~ \E vp2 \in Values : VotedForIn(m1.acc, vp2, c2)
              BY <4>2, <4>3 DEF IndInv, MsgInv
        <5>3. c \in (m1.maxVBal+1)..(m1.bal-1)
          <6>1. m1.maxVBal+1 = 0 BY <4>4
          <6>2. m1.bal - 1 = bbb - 1 BY <4>3
          <6>3. c \in 0..(bbb-1) BY <2>1
          <6>. QED BY <6>1, <6>2, <6>3
        <5>. QED BY <5>2, <5>3, <5>1, <4>2
      <4>. QED BY <4>8, <4>9 DEF WontVoteIn
    <3>. QED BY <3>1
  <2>3. CASE \E c2 \in 0..(bbb-1) :
                  /\ \A m1 \in S : m1.maxVBal =< c2
                  /\ \E m1 \in S : /\ m1.maxVBal = c2 /\ m1.maxVal = vv
    <3>1. PICK c0 \in 0..(bbb-1) :
                /\ \A m1 \in S : m1.maxVBal =< c0
                /\ \E m1 \in S : m1.maxVBal = c0 /\ m1.maxVal = vv
          BY <2>3
    <3>2. PICK ms \in S : ms.maxVBal = c0 /\ ms.maxVal = vv
          BY <3>1
    <3>3. ms.type = "1b" /\ ms.bal = bbb /\ ms \in msgs BY <3>2, <1>S1
    <3>4. ms.acc \in Acceptors BY <3>2, <1>S2
    <3>5. /\ ms.maxVBal \in 0..(ms.bal-1)
          /\ ms.maxVal \in Values
          /\ VotedForIn(ms.acc, ms.maxVal, ms.maxVBal)
      <4>1. \/ (ms.maxVBal = -1 /\ ms.maxVal = None)
            \/ /\ ms.maxVBal \in 0..(ms.bal-1)
               /\ ms.maxVal \in Values
               /\ VotedForIn(ms.acc, ms.maxVal, ms.maxVBal)
            BY <3>2, <3>3 DEF IndInv, MsgInv
      <4>2. ms.maxVBal = c0 BY <3>2
      <4>3. c0 \in 0..(bbb-1) BY <3>1
      <4>4. c0 # -1
            <5>1. bbb \in Nat BY DEF Ballots
            <5>. QED BY <4>3, <5>1
      <4>5. ms.maxVBal # -1 BY <4>2, <4>4
      <4>. QED BY <4>1, <4>5
    <3>6. VotedForIn(ms.acc, vv, c0)
          BY <3>5, <3>2
    <3>7. \E mp \in msgs : mp.type = "2a" /\ mp.bal = c0 /\ mp.val = vv
      <4>1. PICK m2b \in msgs : m2b.type = "2b" /\ m2b.val = vv /\ m2b.bal = c0 /\ m2b.acc = ms.acc
            BY <3>6 DEF VotedForIn
      <4>. QED BY <4>1 DEF IndInv, MsgInv
    <3>8. PICK m2a \in msgs : m2a.type = "2a" /\ m2a.bal = c0 /\ m2a.val = vv
          BY <3>7
    <3>9. SafeAt(vv, c0) BY <3>8 DEF IndInv, MsgInv
    <3>10. CASE c < c0
      <4>1. \E QQ \in Quorums : \A x \in QQ : VotedForIn(x, vv, c) \/ WontVoteIn(x, c)
        <5>1. c \in 0..(c0-1)
              <6>1. c \in 0..(bbb-1) BY <2>1
              <6>2. c0 \in 0..(bbb-1) BY <3>1
              <6>3. bbb \in Nat BY DEF Ballots
              <6>. QED BY <6>1, <6>2, <6>3, <3>10
        <5>. QED BY <5>1, <3>9 DEF SafeAt
      <4>. QED BY <4>1
    <3>11. CASE c = c0
      <4>1. \A x \in Q1 : VotedForIn(x, vv, c0) \/ WontVoteIn(x, c0)
        <5>1. SUFFICES ASSUME NEW x \in Q1
                       PROVE VotedForIn(x, vv, c0) \/ WontVoteIn(x, c0)
              OBVIOUS
        <5>2. PICK m1 \in S : m1.acc = x BY <1>0d, <5>1
        <5>3. m1.type = "1b" /\ m1.bal = bbb /\ m1 \in msgs BY <1>S1, <5>2
        <5>4. m1.maxVBal =< c0 BY <3>1, <5>2
        <5>5. x \in Acceptors BY <5>2, <1>S2
        <5>6. CASE m1.maxVBal = c0
          <6>1. /\ m1.maxVBal \in 0..(m1.bal-1)
                /\ m1.maxVal \in Values
                /\ VotedForIn(m1.acc, m1.maxVal, m1.maxVBal)
            <7>1. \/ (m1.maxVBal = -1 /\ m1.maxVal = None)
                  \/ /\ m1.maxVBal \in 0..(m1.bal-1)
                     /\ m1.maxVal \in Values
                     /\ VotedForIn(m1.acc, m1.maxVal, m1.maxVBal)
                  BY <5>2, <5>3 DEF IndInv, MsgInv
            <7>2. m1.maxVBal = c0 BY <5>6
            <7>3. c0 # -1
                  <8>1. bbb \in Nat BY DEF Ballots
                  <8>2. c0 \in 0..(bbb-1) BY <3>1
                  <8>. QED BY <8>1, <8>2
            <7>4. m1.maxVBal # -1 BY <7>2, <7>3
            <7>. QED BY <7>1, <7>4
          <6>2. VotedForIn(m1.acc, m1.maxVal, c0)
                BY <6>1, <5>6
          <6>3. \E mp \in msgs : mp.type = "2a" /\ mp.bal = c0 /\ mp.val = m1.maxVal
            <7>1. PICK m2bb \in msgs : m2bb.type = "2b" /\ m2bb.val = m1.maxVal /\ m2bb.bal = c0 /\ m2bb.acc = m1.acc
                  BY <6>2 DEF VotedForIn
            <7>. QED BY <7>1 DEF IndInv, MsgInv
          <6>4. m1.maxVal = vv
            <7>1. \A m1a \in msgs, m1b \in msgs :
                    m1a.type = "2a" /\ m1b.type = "2a" /\ m1a.bal = m1b.bal => m1a.val = m1b.val
                  BY DEF IndInv, MsgInv
            <7>. QED BY <6>3, <3>8, <7>1
          <6>. QED BY <6>2, <6>4, <5>2
        <5>7. CASE m1.maxVBal < c0
          <6>1. \A c2 \in (m1.maxVBal+1)..(m1.bal-1) : ~ \E vp2 \in Values : VotedForIn(m1.acc, vp2, c2)
                BY <5>2, <5>3 DEF IndInv, MsgInv
          <6>2. c0 \in (m1.maxVBal+1)..(m1.bal-1)
            <7>0. bbb \in Nat BY DEF Ballots
            <7>1. m1.bal = bbb BY <5>3
            <7>5. c0 \in 0..(bbb-1) /\ c0 \in Nat BY <3>1, <7>0
            <7>2. c0 < m1.bal BY <7>5, <7>1, <7>0
            <7>3. c0 > m1.maxVBal BY <5>7
            <7>4. m1.maxVBal \in Ballots \cup {-1} BY <5>2, <1>S2
            <7>6. m1.maxVBal \in Int BY <7>4 DEF Ballots
            <7>7. m1.maxVBal + 1 \in Int BY <7>6
            <7>8. c0 \in Int BY <7>5
            <7>9. m1.bal \in Int BY <7>1, <7>0
            <7>10. c0 >= m1.maxVBal + 1 BY <7>3, <7>6, <7>8
            <7>11. c0 =< m1.bal - 1 BY <7>2, <7>9, <7>8
            <7>. QED BY <7>10, <7>11, <7>7, <7>9, <7>8
          <6>3. \A vp \in Values : ~ VotedForIn(x, vp, c0)
            <7>1. SUFFICES ASSUME NEW vp \in Values, VotedForIn(x, vp, c0)
                           PROVE FALSE
                  OBVIOUS
            <7>. QED BY <6>1, <6>2, <7>1, <5>2
          <6>4. m1.bal =< maxBal[m1.acc] BY <5>2, <5>3 DEF IndInv, MsgInv
          <6>5. maxBal[m1.acc] >= bbb BY <6>4, <5>3
          <6>6. maxBal[x] >= bbb BY <6>5, <5>2
          <6>7. maxBal[x] > c0
            <7>1. bbb \in Nat BY DEF Ballots
            <7>2. c0 \in 0..(bbb-1) BY <3>1
            <7>3. bbb > c0 BY <7>1, <7>2
            <7>4. maxBal[x] \in Ballots \cup {-1} BY <5>5 DEF IndInv, TypeOK
            <7>. QED BY <6>6, <7>3, <7>1, <7>4 DEF Ballots
          <6>. QED BY <6>3, <6>7 DEF WontVoteIn
        <5>. QED BY <5>4, <5>6, <5>7, <5>2, <1>S2
      <4>2. c = c0 BY <3>11
      <4>3. \A x \in Q1 : VotedForIn(x, vv, c) \/ WontVoteIn(x, c) BY <4>1, <4>2
      <4>. QED BY <4>3
    <3>12. CASE c > c0
      <4>1. \A x \in Q1 : WontVoteIn(x, c)
        <5>1. SUFFICES ASSUME NEW x \in Q1
                       PROVE WontVoteIn(x, c)
              OBVIOUS
        <5>2. PICK m1 \in S : m1.acc = x BY <1>0d, <5>1
        <5>3. m1.type = "1b" /\ m1.bal = bbb /\ m1 \in msgs BY <1>S1, <5>2
        <5>3a. bbb \in Nat /\ c \in Nat BY <2>1 DEF Ballots
        <5>4. m1.maxVBal =< c0 BY <3>1, <5>2
        <5>4a. m1.maxVBal \in Ballots \cup {-1} BY <5>2, <1>S2
        <5>4b. c0 \in Nat /\ m1.maxVBal \in Int
               BY <3>1, <5>3a, <5>4a DEF Ballots
        <5>5. x \in Acceptors BY <5>2, <1>S2
        <5>6. m1.maxVBal < c BY <5>4, <3>12, <5>4b, <5>3a
        <5>7. \A c2 \in (m1.maxVBal+1)..(m1.bal-1) : ~ \E vp2 \in Values : VotedForIn(m1.acc, vp2, c2)
              BY <5>2, <5>3 DEF IndInv, MsgInv
        <5>8. c \in (m1.maxVBal+1)..(m1.bal-1)
          <6>1. m1.bal = bbb BY <5>3
          <6>2. c < bbb BY <2>1, <5>3a
          <6>3. c > m1.maxVBal BY <5>6
          <6>4. m1.maxVBal + 1 \in Int BY <5>4b
          <6>5. c >= m1.maxVBal + 1 BY <6>3, <5>3a, <5>4b
          <6>6. c =< m1.bal - 1
                <7>1. m1.bal \in Int BY <6>1, <5>3a
                <7>. QED BY <6>2, <5>3a, <6>1, <7>1
          <6>. QED BY <6>5, <6>6, <6>4, <6>1, <5>3a
        <5>9. \A vp \in Values : ~ VotedForIn(x, vp, c)
          <6>1. SUFFICES ASSUME NEW vp \in Values, VotedForIn(x, vp, c)
                         PROVE FALSE
                OBVIOUS
          <6>. QED BY <5>7, <5>8, <6>1, <5>2
        <5>10. m1.bal =< maxBal[m1.acc] BY <5>2, <5>3 DEF IndInv, MsgInv
        <5>11. maxBal[m1.acc] >= bbb BY <5>10, <5>3
        <5>12. maxBal[x] >= bbb BY <5>11, <5>2
        <5>13. maxBal[x] > c
          <6>2. c \in Nat /\ bbb \in Nat BY <2>1 DEF Ballots
          <6>1. c < bbb BY <2>1, <6>2
          <6>3. maxBal[x] \in Ballots \cup {-1} BY <5>5 DEF IndInv, TypeOK
          <6>. QED BY <5>12, <6>1, <6>2, <6>3 DEF Ballots
        <5>. QED BY <5>9, <5>13 DEF WontVoteIn
      <4>. QED BY <4>1
    <3>13. c \in Nat /\ c0 \in Nat
           BY <2>1, <3>1 DEF Ballots
    <3>. QED BY <3>10, <3>11, <3>12, <3>13
  <2>. QED BY <1>0d, <2>2, <2>3
<1>5p. SafeAt(vv, bbb)'
  <2>1. SUFFICES ASSUME NEW c \in 0..(bbb-1)
                 PROVE \E QQ \in Quorums :
                         \A x \in QQ : VotedForIn(x, vv, c)' \/ WontVoteIn(x, c)'
        BY DEF SafeAt
  <2>2. PICK QQ \in Quorums : \A x \in QQ : VotedForIn(x, vv, c) \/ WontVoteIn(x, c)
        BY <1>5, <2>1 DEF SafeAt
  <2>3. QQ \subseteq Acceptors BY QuorumAssumption
  <2>4. \A x \in QQ : VotedForIn(x, vv, c)' \/ WontVoteIn(x, c)'
    <3>1. SUFFICES ASSUME NEW x \in QQ
                   PROVE VotedForIn(x, vv, c)' \/ WontVoteIn(x, c)'
          OBVIOUS
    <3>2. x \in Acceptors BY <2>3, <3>1
    <3>3. CASE VotedForIn(x, vv, c)
          BY <3>3, <1>m DEF VotedForIn
    <3>4. CASE WontVoteIn(x, c)
      <4>1. \A vp \in Values : ~ VotedForIn(x, vp, c) BY <3>4 DEF WontVoteIn
      <4>2. maxBal[x] > c BY <3>4 DEF WontVoteIn
      <4>3. maxBal'[x] > c BY <4>2, <1>2
      <4>4. \A vp \in Values : ~ VotedForIn(x, vp, c)'
        <5>1. SUFFICES ASSUME NEW vp \in Values, VotedForIn(x, vp, c)'
                       PROVE FALSE
              OBVIOUS
        <5>2. PICK m2 \in msgs' : m2.type = "2b" /\ m2.val = vp /\ m2.bal = c /\ m2.acc = x
              BY <5>1 DEF VotedForIn
        <5>3. m2 \in msgs BY <1>1, <5>2
        <5>4. VotedForIn(x, vp, c) BY <5>2, <5>3 DEF VotedForIn
        <5>. QED BY <5>4, <4>1, <5>1
      <4>. QED BY <4>3, <4>4 DEF WontVoteIn
    <3>. QED BY <2>2, <3>1, <3>3, <3>4
  <2>. QED BY <2>4
<1>6. MsgInv'
  <2>1. SUFFICES ASSUME NEW mm \in msgs' PROVE
          /\ (mm.type = "1b") =>
               /\ mm.bal =< maxBal'[mm.acc]
               /\ \/ (mm.maxVBal = -1 /\ mm.maxVal = None)
                  \/ /\ mm.maxVBal \in 0..(mm.bal-1)
                     /\ mm.maxVal \in Values
                     /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
               /\ \A c \in (mm.maxVBal+1)..(mm.bal-1) :
                    ~ \E v \in Values : VotedForIn(mm.acc, v, c)'
          /\ (mm.type = "2a") =>
               /\ SafeAt(mm.val, mm.bal)'
               /\ \A m2 \in msgs' :
                    (m2.type = "2a") /\ (m2.bal = mm.bal) => m2.val = mm.val
          /\ (mm.type = "2b") =>
               /\ \E m2 \in msgs' : /\ m2.type = "2a"
                                    /\ m2.bal = mm.bal
                                    /\ m2.val = mm.val
               /\ mm.bal =< maxVBal'[mm.acc]
        BY DEF MsgInv
  <2>SA. ASSUME NEW v0, NEW b0, SafeAt(v0, b0)
         PROVE  SafeAt(v0, b0)'
    <3>1. SUFFICES ASSUME NEW c \in 0..(b0-1)
                   PROVE \E QQ \in Quorums :
                           \A x \in QQ : VotedForIn(x, v0, c)' \/ WontVoteIn(x, c)'
          BY DEF SafeAt
    <3>2. PICK QQ \in Quorums : \A x \in QQ : VotedForIn(x, v0, c) \/ WontVoteIn(x, c)
          BY <2>SA, <3>1 DEF SafeAt
    <3>3. QQ \subseteq Acceptors BY QuorumAssumption
    <3>4. \A x \in QQ : VotedForIn(x, v0, c)' \/ WontVoteIn(x, c)'
      <4>1. SUFFICES ASSUME NEW x \in QQ
                     PROVE VotedForIn(x, v0, c)' \/ WontVoteIn(x, c)'
            OBVIOUS
      <4>2. x \in Acceptors BY <3>3, <4>1
      <4>3. CASE VotedForIn(x, v0, c)
            BY <4>3, <1>m DEF VotedForIn
      <4>4. CASE WontVoteIn(x, c)
        <5>1. \A vp \in Values : ~ VotedForIn(x, vp, c) BY <4>4 DEF WontVoteIn
        <5>2. maxBal[x] > c BY <4>4 DEF WontVoteIn
        <5>3. maxBal'[x] > c BY <5>2, <1>2
        <5>4. \A vp \in Values : ~ VotedForIn(x, vp, c)'
          <6>1. SUFFICES ASSUME NEW vp \in Values, VotedForIn(x, vp, c)'
                         PROVE FALSE
                OBVIOUS
          <6>2. PICK m2 \in msgs' : m2.type = "2b" /\ m2.val = vp /\ m2.bal = c /\ m2.acc = x
                BY <6>1 DEF VotedForIn
          <6>3. m2 \in msgs BY <1>1, <6>2
          <6>4. VotedForIn(x, vp, c) BY <6>2, <6>3 DEF VotedForIn
          <6>. QED BY <6>4, <5>1, <6>1
        <5>. QED BY <5>3, <5>4 DEF WontVoteIn
      <4>. QED BY <3>2, <4>1, <4>3, <4>4
    <3>. QED BY <3>4
  <2>2. CASE mm \notin msgs
    <3>1. mm = [type |-> "2a", bal |-> bbb, val |-> vv]
          BY <1>1, <2>2
    <3>2. mm.type = "2a" /\ mm.bal = bbb /\ mm.val = vv
          BY <3>1
    <3>3. SafeAt(mm.val, mm.bal)'
          BY <3>2, <1>5p
    <3>4. \A m2 \in msgs' : (m2.type = "2a") /\ (m2.bal = mm.bal) => m2.val = mm.val
      <4>1. SUFFICES ASSUME NEW m2 \in msgs', m2.type = "2a", m2.bal = mm.bal
                     PROVE m2.val = mm.val
            OBVIOUS
      <4>2. m2.bal = bbb BY <3>2, <4>1
      <4>3. CASE m2 \in msgs
            <5>1. ~ \E mp \in msgs : mp.type = "2a" /\ mp.bal = bbb BY <1>0a
            <5>. QED BY <4>3, <4>2, <5>1, <4>1
      <4>4. CASE m2 \notin msgs
            <5>1. m2 = [type |-> "2a", bal |-> bbb, val |-> vv] BY <1>1, <4>4
            <5>. QED BY <5>1, <3>1
      <4>. QED BY <4>3, <4>4
    <3>. QED BY <3>2, <3>3, <3>4
  <2>3. CASE mm \in msgs
    <3>0. mm \in Messages BY <2>3 DEF IndInv, TypeOK
    <3>1. CASE mm.type = "1b"
      <4>1. mm.acc \in Acceptors BY <3>0, <3>1 DEF Messages
      <4>2. /\ mm.bal =< maxBal[mm.acc]
            /\ \/ (mm.maxVBal = -1 /\ mm.maxVal = None)
               \/ /\ mm.maxVBal \in 0..(mm.bal-1)
                  /\ mm.maxVal \in Values
                  /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
            /\ \A c \in (mm.maxVBal+1)..(mm.bal-1) :
                 ~ \E v \in Values : VotedForIn(mm.acc, v, c)
            BY <3>1, <2>3 DEF IndInv, MsgInv
      <4>3. mm.bal =< maxBal'[mm.acc] BY <4>2, <1>2
      <4>4. \/ (mm.maxVBal = -1 /\ mm.maxVal = None)
            \/ /\ mm.maxVBal \in 0..(mm.bal-1)
               /\ mm.maxVal \in Values
               /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
            BY <4>2, <1>m DEF VotedForIn
      <4>5. \A c \in (mm.maxVBal+1)..(mm.bal-1) :
                 ~ \E v \in Values : VotedForIn(mm.acc, v, c)'
        <5>1. SUFFICES ASSUME NEW c \in (mm.maxVBal+1)..(mm.bal-1),
                              NEW v \in Values, VotedForIn(mm.acc, v, c)'
                       PROVE FALSE
              OBVIOUS
        <5>2. PICK m2 \in msgs' : m2.type = "2b" /\ m2.val = v /\ m2.bal = c /\ m2.acc = mm.acc
              BY <5>1 DEF VotedForIn
        <5>3. m2 \in msgs BY <1>1, <5>2
        <5>4. VotedForIn(mm.acc, v, c) BY <5>2, <5>3 DEF VotedForIn
        <5>. QED BY <4>2, <5>1, <5>4
      <4>. QED BY <3>1, <4>3, <4>4, <4>5
    <3>2. CASE mm.type = "2a"
      <4>0. mm.val \in Values /\ mm.bal \in Ballots BY <3>0, <3>2 DEF Messages
      <4>1. SafeAt(mm.val, mm.bal) BY <3>2, <2>3 DEF IndInv, MsgInv
      <4>2. SafeAt(mm.val, mm.bal)' BY <2>SA, <4>1
      <4>3. \A m2 \in msgs' : (m2.type = "2a") /\ (m2.bal = mm.bal) => m2.val = mm.val
        <5>1. SUFFICES ASSUME NEW m2 \in msgs', m2.type = "2a", m2.bal = mm.bal
                       PROVE m2.val = mm.val
              OBVIOUS
        <5>2. CASE m2 \in msgs
              BY <2>3, <3>2, <5>1, <5>2 DEF IndInv, MsgInv
        <5>3. CASE m2 \notin msgs
          <6>1. m2 = [type |-> "2a", bal |-> bbb, val |-> vv] BY <1>1, <5>3
          <6>2. m2.bal = bbb /\ m2.val = vv BY <6>1
          <6>3. mm.bal = bbb BY <5>1, <6>2
          <6>4. ~ \E mp \in msgs : mp.type = "2a" /\ mp.bal = bbb BY <1>0a
          <6>. QED BY <2>3, <3>2, <6>3, <6>4
        <5>. QED BY <5>2, <5>3
      <4>. QED BY <3>2, <4>2, <4>3
    <3>3. CASE mm.type = "2b"
      <4>0. mm.acc \in Acceptors BY <3>0, <3>3 DEF Messages
      <4>1. \E m2 \in msgs : /\ m2.type = "2a"
                             /\ m2.bal = mm.bal
                             /\ m2.val = mm.val
            BY <3>3, <2>3 DEF IndInv, MsgInv
      <4>2. mm.bal =< maxVBal[mm.acc] BY <3>3, <2>3 DEF IndInv, MsgInv
      <4>. QED BY <3>3, <4>1, <4>2, <1>1, <1>2
    <3>. QED BY <3>1, <3>2, <3>3, <3>0 DEF Messages
  <2>. QED BY <2>2, <2>3
<1>. QED BY <1>3, <1>4, <1>6 DEF IndInv

-----------------------------------------------------------------------------
\* Inductive invariant preserved by the spec

LEMMA NextInv ==
  ASSUME IndInv, [Next]_vars
  PROVE  IndInv'
<1>1. CASE Next
  <2>1. CASE \E b \in Ballots : Phase1a(b)
        BY <2>1, Phase1aInv
  <2>2. CASE \E b \in Ballots : Phase2a(b)
        BY <2>2, Phase2aInv
  <2>3. CASE \E a \in Acceptors : Phase1b(a)
        BY <2>3, Phase1bInv
  <2>4. CASE \E a \in Acceptors : Phase2b(a)
        BY <2>4, Phase2bInv
  <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF Next
<1>2. CASE UNCHANGED vars
      BY <1>2 DEF IndInv, TypeOK, MsgInv, AccInv, SafeAt, WontVoteIn, VotedForIn, vars
<1>. QED BY <1>1, <1>2

-----------------------------------------------------------------------------
\* Spec implies always IndInv

THEOREM SpecImpliesIndInv == Spec => []IndInv
<1>1. Init => IndInv BY InitInv
<1>2. IndInv /\ [Next]_vars => IndInv' BY NextInv
<1>. QED BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
\* Consistency: at most one value chosen

LEMMA Consistency ==
  ASSUME IndInv, NEW v1 \in Values, NEW v2 \in Values, Chosen(v1), Chosen(v2)
  PROVE  v1 = v2
<1>1. PICK b1 \in Ballots : ChosenIn(v1, b1) BY DEF Chosen
<1>2. PICK b2 \in Ballots : ChosenIn(v2, b2) BY DEF Chosen
<1>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1) BY <1>1 DEF ChosenIn
<1>4. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2) BY <1>2 DEF ChosenIn
<1>5. b1 \in Nat /\ b2 \in Nat BY DEF Ballots
\* Symmetric lemma: if v is chosen at b and SafeAt(w, b') with b' > b, then v = w.
<1>SafeAtImplies. ASSUME NEW v, NEW b \in Ballots, NEW w, NEW b2x \in Ballots,
                          ChosenIn(v, b), SafeAt(w, b2x), b < b2x,
                          \E mp \in msgs : mp.type = "2a" /\ mp.bal = b2x /\ mp.val = w
                  PROVE  v = w
  <2>0. v \in Values
    <3>1. PICK QQ \in Quorums : \A a \in QQ : VotedForIn(a, v, b)
          BY <1>SafeAtImplies DEF ChosenIn
    <3>2. QQ # {}
          <4>1. PICK QQ2 \in Quorums : TRUE BY QuorumAssumption
          <4>2. QQ \cap QQ2 # {} BY QuorumAssumption
          <4>. QED BY <4>2
    <3>3. PICK a \in QQ : VotedForIn(a, v, b)
          BY <3>1, <3>2
    <3>4. a \in Acceptors BY <3>3, QuorumAssumption
    <3>. QED BY <3>3, <3>4 DEF IndInv, TypeOK, VotedForIn, Messages
  <2>1. PICK QQc \in Quorums : \A a \in QQc : VotedForIn(a, v, b)
        BY <1>SafeAtImplies DEF ChosenIn
  <2>2. b \in 0..(b2x - 1)
        <3>1. b2x \in Nat /\ b \in Nat BY DEF Ballots
        <3>. QED BY <1>SafeAtImplies, <3>1
  <2>3. PICK QQs \in Quorums : \A a \in QQs : VotedForIn(a, w, b) \/ WontVoteIn(a, b)
        BY <2>2, <1>SafeAtImplies DEF SafeAt
  <2>4. QQc \cap QQs # {} BY QuorumAssumption
  <2>5. PICK a \in QQc \cap QQs : TRUE BY <2>4
  <2>6. a \in Acceptors BY <2>5, QuorumAssumption
  <2>7. VotedForIn(a, v, b) BY <2>5, <2>1
  <2>8. VotedForIn(a, w, b) \/ WontVoteIn(a, b) BY <2>5, <2>3
  <2>9. VotedForIn(a, w, b)
        <3>1. ~ WontVoteIn(a, b)
          <4>1. SUFFICES WontVoteIn(a, b) => FALSE OBVIOUS
          <4>2. ASSUME WontVoteIn(a, b)
                PROVE  FALSE
                <5>1. \A vp \in Values : ~ VotedForIn(a, vp, b) BY <4>2 DEF WontVoteIn
                <5>. QED BY <5>1, <2>7, <2>0
          <4>. QED BY <4>2
        <3>. QED BY <2>8, <3>1
  <2>. QED BY <2>7, <2>9, <2>6, VotedOnce
\* Use the SafeAtImplies for the actual proof
<1>6. CASE b1 = b2
  <2>1. PICK a1 \in Q1, a2 \in Q2 : a1 \in Q1 \cap Q2
        <3>1. Q1 \cap Q2 # {} BY QuorumAssumption
        <3>. QED BY <3>1
  <2>2. PICK a \in Q1 \cap Q2 : TRUE
        <3>1. Q1 \cap Q2 # {} BY QuorumAssumption
        <3>. QED BY <3>1
  <2>3. VotedForIn(a, v1, b1) /\ VotedForIn(a, v2, b2) BY <2>2, <1>3, <1>4
  <2>4. a \in Acceptors BY <2>2, QuorumAssumption
  <2>. QED BY <2>3, <2>4, <1>6, VotedOnce
<1>7. CASE b1 < b2
  <2>0. Q2 # {}
        <3>1. PICK QQ \in Quorums : TRUE BY QuorumAssumption
        <3>2. Q2 \cap QQ # {} BY <3>1, QuorumAssumption
        <3>. QED BY <3>2
  <2>1. PICK a \in Q2 : VotedForIn(a, v2, b2) BY <1>4, <2>0
  <2>2. a \in Acceptors BY <2>1, QuorumAssumption
  <2>3. PICK mp \in msgs : mp.type = "2a" /\ mp.bal = b2 /\ mp.val = v2
        BY <2>1, <2>2, VotedInv
  <2>4. SafeAt(v2, b2) BY <2>3 DEF IndInv, MsgInv
  <2>. QED BY <1>1, <2>4, <2>3, <1>7, <1>5, <1>SafeAtImplies
<1>8. CASE b2 < b1
  <2>0. Q1 # {}
        <3>1. PICK QQ \in Quorums : TRUE BY QuorumAssumption
        <3>2. Q1 \cap QQ # {} BY <3>1, QuorumAssumption
        <3>. QED BY <3>2
  <2>1. PICK a \in Q1 : VotedForIn(a, v1, b1) BY <1>3, <2>0
  <2>2. a \in Acceptors BY <2>1, QuorumAssumption
  <2>3. PICK mp \in msgs : mp.type = "2a" /\ mp.bal = b1 /\ mp.val = v1
        BY <2>1, <2>2, VotedInv
  <2>4. SafeAt(v1, b1) BY <2>3 DEF IndInv, MsgInv
  <2>5. v2 = v1 BY <1>2, <2>4, <2>3, <1>8, <1>5, <1>SafeAtImplies
  <2>. QED BY <2>5
<1>. QED BY <1>5, <1>6, <1>7, <1>8

-----------------------------------------------------------------------------
\* Primed version of Consistency
\* Since IndInv' is a state predicate (just with primed variables),
\* and so are Chosen(v1)' and Chosen(v2)', we can apply the same reasoning.

LEMMA ConsistencyPrime ==
  ASSUME IndInv', NEW v1 \in Values, NEW v2 \in Values, Chosen(v1)', Chosen(v2)'
  PROVE  v1 = v2
<1>1. PICK b1 \in Ballots : ChosenIn(v1, b1)' BY DEF Chosen
<1>2. PICK b2 \in Ballots : ChosenIn(v2, b2)' BY DEF Chosen
<1>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)' BY <1>1 DEF ChosenIn
<1>4. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)' BY <1>2 DEF ChosenIn
<1>5. b1 \in Nat /\ b2 \in Nat BY DEF Ballots
<1>VotedOncePrime. ASSUME NEW aa1 \in Acceptors, NEW aa2 \in Acceptors,
                          NEW vv1, NEW vv2, NEW bb,
                          VotedForIn(aa1, vv1, bb)', VotedForIn(aa2, vv2, bb)'
                   PROVE  vv1 = vv2
  <2>1. PICK m11 \in msgs' : m11.type = "2b" /\ m11.val = vv1 /\ m11.bal = bb /\ m11.acc = aa1
        BY <1>VotedOncePrime DEF VotedForIn
  <2>2. PICK m12 \in msgs' : m12.type = "2b" /\ m12.val = vv2 /\ m12.bal = bb /\ m12.acc = aa2
        BY <1>VotedOncePrime DEF VotedForIn
  <2>3. \E mm \in msgs' : mm.type = "2a" /\ mm.bal = bb /\ mm.val = vv1
        BY <2>1 DEF IndInv, MsgInv
  <2>4. \E mm \in msgs' : mm.type = "2a" /\ mm.bal = bb /\ mm.val = vv2
        BY <2>2 DEF IndInv, MsgInv
  <2>. QED BY <2>3, <2>4 DEF IndInv, MsgInv
<1>SafeAtPrime. ASSUME NEW v, NEW b \in Ballots, NEW w, NEW b2x \in Ballots,
                       ChosenIn(v, b)', SafeAt(w, b2x)', b < b2x,
                       \E mp \in msgs' : mp.type = "2a" /\ mp.bal = b2x /\ mp.val = w
                PROVE  v = w
  <2>0. v \in Values
    <3>1. PICK QQ \in Quorums : \A a \in QQ : VotedForIn(a, v, b)'
          BY <1>SafeAtPrime DEF ChosenIn
    <3>2. QQ # {}
          <4>1. PICK QQ2 \in Quorums : TRUE BY QuorumAssumption
          <4>2. QQ \cap QQ2 # {} BY QuorumAssumption
          <4>. QED BY <4>2
    <3>3. PICK a \in QQ : VotedForIn(a, v, b)' BY <3>1, <3>2
    <3>4. a \in Acceptors BY <3>3, QuorumAssumption
    <3>5. PICK mm \in msgs' : mm.type = "2b" /\ mm.val = v /\ mm.bal = b /\ mm.acc = a
          BY <3>3 DEF VotedForIn
    <3>6. mm \in Messages BY <3>5 DEF IndInv, TypeOK
    <3>. QED BY <3>5, <3>6 DEF Messages
  <2>1. PICK QQc \in Quorums : \A a \in QQc : VotedForIn(a, v, b)'
        BY <1>SafeAtPrime DEF ChosenIn
  <2>2. b \in 0..(b2x - 1)
        <3>1. b2x \in Nat /\ b \in Nat BY DEF Ballots
        <3>. QED BY <1>SafeAtPrime, <3>1
  <2>3. PICK QQs \in Quorums : \A a \in QQs : VotedForIn(a, w, b)' \/ WontVoteIn(a, b)'
        BY <2>2, <1>SafeAtPrime DEF SafeAt
  <2>4. QQc \cap QQs # {} BY QuorumAssumption
  <2>5. PICK a \in QQc \cap QQs : TRUE BY <2>4
  <2>6. a \in Acceptors BY <2>5, QuorumAssumption
  <2>7. VotedForIn(a, v, b)' BY <2>5, <2>1
  <2>8. VotedForIn(a, w, b)' \/ WontVoteIn(a, b)' BY <2>5, <2>3
  <2>9. VotedForIn(a, w, b)'
        <3>1. ~ WontVoteIn(a, b)'
          <4>1. SUFFICES WontVoteIn(a, b)' => FALSE OBVIOUS
          <4>2. ASSUME WontVoteIn(a, b)'
                PROVE  FALSE
                <5>1. \A vp \in Values : ~ VotedForIn(a, vp, b)' BY <4>2 DEF WontVoteIn
                <5>. QED BY <5>1, <2>7, <2>0
          <4>. QED BY <4>2
        <3>. QED BY <2>8, <3>1
  <2>. QED BY <2>7, <2>9, <2>6, <1>VotedOncePrime
<1>6. CASE b1 = b2
  <2>1. PICK a \in Q1, a2 \in Q2 : a \in Q1 \cap Q2
        <3>1. Q1 \cap Q2 # {} BY QuorumAssumption
        <3>. QED BY <3>1
  <2>2. PICK a \in Q1 \cap Q2 : TRUE
        <3>1. Q1 \cap Q2 # {} BY QuorumAssumption
        <3>. QED BY <3>1
  <2>3. VotedForIn(a, v1, b1)' /\ VotedForIn(a, v2, b2)' BY <2>2, <1>3, <1>4
  <2>4. a \in Acceptors BY <2>2, QuorumAssumption
  <2>. QED BY <2>3, <2>4, <1>6, <1>VotedOncePrime
<1>7. CASE b1 < b2
  <2>0. Q2 # {}
        <3>1. PICK QQ \in Quorums : TRUE BY QuorumAssumption
        <3>2. Q2 \cap QQ # {} BY <3>1, QuorumAssumption
        <3>. QED BY <3>2
  <2>1. PICK a \in Q2 : VotedForIn(a, v2, b2)' BY <1>4, <2>0
  <2>2. a \in Acceptors BY <2>1, QuorumAssumption
  <2>3. PICK m22 \in msgs' : m22.type = "2b" /\ m22.val = v2 /\ m22.bal = b2 /\ m22.acc = a
        BY <2>1 DEF VotedForIn
  <2>4. PICK mp \in msgs' : mp.type = "2a" /\ mp.bal = b2 /\ mp.val = v2
        BY <2>3 DEF IndInv, MsgInv
  <2>5. SafeAt(v2, b2)' BY <2>4 DEF IndInv, MsgInv
  <2>. QED BY <1>1, <2>5, <2>4, <1>7, <1>5, <1>SafeAtPrime
<1>8. CASE b2 < b1
  <2>0. Q1 # {}
        <3>1. PICK QQ \in Quorums : TRUE BY QuorumAssumption
        <3>2. Q1 \cap QQ # {} BY <3>1, QuorumAssumption
        <3>. QED BY <3>2
  <2>1. PICK a \in Q1 : VotedForIn(a, v1, b1)' BY <1>3, <2>0
  <2>2. a \in Acceptors BY <2>1, QuorumAssumption
  <2>3. PICK m22 \in msgs' : m22.type = "2b" /\ m22.val = v1 /\ m22.bal = b1 /\ m22.acc = a
        BY <2>1 DEF VotedForIn
  <2>4. PICK mp \in msgs' : mp.type = "2a" /\ mp.bal = b1 /\ mp.val = v1
        BY <2>3 DEF IndInv, MsgInv
  <2>5. SafeAt(v1, b1)' BY <2>4 DEF IndInv, MsgInv
  <2>6. v2 = v1 BY <1>2, <2>5, <2>4, <1>8, <1>5, <1>SafeAtPrime
  <2>. QED BY <2>6
<1>. QED BY <1>5, <1>6, <1>7, <1>8

-----------------------------------------------------------------------------
\* Refinement: Spec => C!Spec

THEOREM Refinement == Spec => C!Spec
<1>1. Init => C!Init
  <2>1. SUFFICES ASSUME Init PROVE chosenBar = {}
        BY DEF C!Init
  <2>2. \A v \in Values : ~ Chosen(v)
    <3>1. SUFFICES ASSUME NEW v \in Values, Chosen(v) PROVE FALSE OBVIOUS
    <3>2. msgs = {} BY <2>1 DEF Init
    <3>3. PICK b \in Ballots : ChosenIn(v, b) BY <3>1 DEF Chosen
    <3>4. PICK QQ \in Quorums : \A a \in QQ : VotedForIn(a, v, b)
          BY <3>3 DEF ChosenIn
    <3>5. QQ # {}
          <4>1. PICK QQ2 \in Quorums : TRUE BY QuorumAssumption
          <4>2. QQ \cap QQ2 # {} BY QuorumAssumption
          <4>. QED BY <4>2
    <3>6. PICK a \in QQ : VotedForIn(a, v, b) BY <3>4, <3>5
    <3>. QED BY <3>6, <3>2 DEF VotedForIn
  <2>. QED BY <2>2 DEF chosenBar
<1>2. IndInv /\ IndInv' /\ [Next]_vars =>
        [chosenBar' = chosenBar \/ (chosenBar = {} /\ \E v \in Values : chosenBar' = {v})]_chosenBar
  <2>1. SUFFICES ASSUME IndInv, IndInv', [Next]_vars
                 PROVE  /\ chosenBar' = chosenBar
                        \/ /\ chosenBar = {}
                           /\ \E v \in Values : chosenBar' = {v}
                        \/ chosenBar' = chosenBar
        OBVIOUS
  <2>m. msgs \subseteq msgs'
    <3>1. CASE Next
      <4>1. CASE \E b \in Ballots : Phase1a(b)
        <5>1. PICK b \in Ballots : Phase1a(b) BY <4>1
        <5>2. msgs' = msgs \cup {[type |-> "1a", bal |-> b]}
              BY <5>1 DEF Phase1a, Send
        <5>. QED BY <5>2
      <4>2. CASE \E b \in Ballots : Phase2a(b)
        <5>1. PICK b \in Ballots : Phase2a(b) BY <4>2
        <5>2. PICK vp \in Values :
                /\ Send([type |-> "2a", bal |-> b, val |-> vp])
              BY <5>1 DEF Phase2a
        <5>3. msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> vp]}
              BY <5>2 DEF Send
        <5>. QED BY <5>3
      <4>3. CASE \E a \in Acceptors : Phase1b(a)
        <5>1. PICK a \in Acceptors : Phase1b(a) BY <4>3
        <5>2. PICK mp \in msgs : Send([type |-> "1b", bal |-> mp.bal,
                                       maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a])
              BY <5>1 DEF Phase1b
        <5>3. msgs' = msgs \cup {[type |-> "1b", bal |-> mp.bal,
                                  maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a]}
              BY <5>2 DEF Send
        <5>. QED BY <5>3
      <4>4. CASE \E a \in Acceptors : Phase2b(a)
        <5>1. PICK a \in Acceptors : Phase2b(a) BY <4>4
        <5>2. PICK mp \in msgs : Send([type |-> "2b", bal |-> mp.bal,
                                        val |-> mp.val, acc |-> a])
              BY <5>1 DEF Phase2b
        <5>3. msgs' = msgs \cup {[type |-> "2b", bal |-> mp.bal,
                                  val |-> mp.val, acc |-> a]}
              BY <5>2 DEF Send
        <5>. QED BY <5>3
      <4>. QED BY <3>1, <4>1, <4>2, <4>3, <4>4 DEF Next
    <3>2. CASE UNCHANGED vars
          BY <3>2 DEF vars
    <3>. QED BY <3>1, <3>2, <2>1
  <2>2. chosenBar \subseteq chosenBar'
    <3>1. SUFFICES ASSUME NEW v \in chosenBar PROVE v \in chosenBar'
          OBVIOUS
    <3>2. v \in Values /\ Chosen(v) BY <3>1 DEF chosenBar
    <3>3. PICK b \in Ballots : ChosenIn(v, b) BY <3>2 DEF Chosen
    <3>4. PICK QQ \in Quorums : \A a \in QQ : VotedForIn(a, v, b)
          BY <3>3 DEF ChosenIn
    <3>5. \A a \in QQ : VotedForIn(a, v, b)'
      <4>1. SUFFICES ASSUME NEW a \in QQ PROVE VotedForIn(a, v, b)'
            OBVIOUS
      <4>2. VotedForIn(a, v, b) BY <3>4, <4>1
      <4>. QED BY <4>2, <2>m DEF VotedForIn
    <3>6. ChosenIn(v, b)' BY <3>5 DEF ChosenIn
    <3>7. Chosen(v)' BY <3>6, <3>3 DEF Chosen
    <3>. QED BY <3>2, <3>7 DEF chosenBar
  <2>3. chosenBar' \subseteq Values BY DEF chosenBar
  <2>4. \A v1 \in chosenBar', v2 \in chosenBar' : v1 = v2
    <3>1. SUFFICES ASSUME NEW v1 \in chosenBar', NEW v2 \in chosenBar'
                   PROVE v1 = v2
          OBVIOUS
    <3>2. v1 \in Values /\ Chosen(v1)' /\ v2 \in Values /\ Chosen(v2)'
          BY <3>1 DEF chosenBar
    <3>3. IndInv' BY <2>1
    <3>. QED BY <3>2, <3>3, ConsistencyPrime
  <2>5. \/ chosenBar' = chosenBar
        \/ /\ chosenBar = {}
           /\ \E v \in Values : chosenBar' = {v}
    <3>1. CASE chosenBar' = chosenBar
          BY <3>1
    <3>2. CASE chosenBar' # chosenBar
      <4>1. \E v \in chosenBar' \ chosenBar : TRUE
            BY <3>2, <2>2
      <4>2. PICK vx \in chosenBar' : vx \notin chosenBar
            BY <4>1
      <4>3. \A v \in chosenBar' : v = vx
            BY <4>2, <2>4
      <4>4. chosenBar' = {vx}
            <5>1. chosenBar' # {} BY <4>2
            <5>. QED BY <4>3, <5>1
      <4>5. chosenBar = {}
            <5>1. SUFFICES ASSUME NEW vc \in chosenBar
                           PROVE FALSE
                  OBVIOUS
            <5>2. vc \in chosenBar' BY <5>1, <2>2
            <5>3. vc = vx BY <5>2, <4>3
            <5>. QED BY <5>3, <5>1, <4>2
      <4>6. vx \in Values BY <4>2, <2>3
      <4>. QED BY <4>4, <4>5, <4>6
    <3>. QED BY <3>1, <3>2
  <2>. QED BY <2>5
<1>3. Spec => [][C!Next]_chosenBar
  <2>1. Spec => []IndInv BY SpecImpliesIndInv
  <2>2. Spec => [][Next]_vars BY DEF Spec
  <2>3. IndInv /\ IndInv' /\ [Next]_vars => [C!Next]_chosenBar
        BY <1>2 DEF C!Next
  <2>. QED BY <2>1, <2>2, <2>3, PTL
<1>. QED BY <1>1, <1>3, PTL DEF Spec, C!Spec
=============================================================================
