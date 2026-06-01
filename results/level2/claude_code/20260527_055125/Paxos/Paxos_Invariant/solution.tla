------------------------------- MODULE Paxos_Invariant -------------------------------

EXTENDS Integers, TLAPS, TLC
-----------------------------------------------------------------------------
CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == Nat

None == CHOOSE v : v \notin Values

Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]
-----------------------------------------------------------------------------
VARIABLES msgs,
          maxBal,
          maxVBal,
          maxVal

vars == <<msgs, maxBal, maxVBal, maxVal>>

TypeOK == /\ msgs \in SUBSET Messages
          /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxBal \in  [Acceptors -> Ballots \cup {-1}]
          /\ maxVal \in  [Acceptors -> Values \cup {None}]
          /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]

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

-----------------------------------------------------------------------------
WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ maxBal[a] > b

SafeAt(v, b) ==
  \A c \in 0..(b-1) :
    \E Q \in Quorums :
      \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
-----------------------------------------------------------------------------
MsgInv ==
  \A m \in msgs :
    /\ (m.type = "1b") => /\ m.bal =< maxBal[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots

                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)

                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1

                          /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                ~ \E v \in Values : VotedForIn(m.acc, v, c)
    /\ (m.type = "2a") =>
         /\ SafeAt(m.val, m.bal)
         /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
    /\ (m.type = "2b") =>
         /\ \E ma \in msgs : /\ ma.type = "2a"
                             /\ ma.bal  = m.bal
                             /\ ma.val  = m.val
         /\ m.bal =< maxVBal[m.acc]
-----------------------------------------------------------------------------

AccInv ==
  \A a \in Acceptors:
    /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
    /\ maxVBal[a] =< maxBal[a]

    /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])

    /\ \A c \in Ballots : c > maxVBal[a] => ~ \E v \in Values : VotedForIn(a, v, c)
-----------------------------------------------------------------------------
Inv == TypeOK /\ MsgInv /\ AccInv
-----------------------------------------------------------------------------

LEMMA NoneNotAValue == None \notin Values
  BY NoSetContainsEverything DEF None

(* When msgs grows monotonically, VotedForIn is preserved. *)
LEMMA VotedForIn_Mono ==
  ASSUME NEW aa, NEW vv, NEW cc,
         msgs \subseteq msgs',
         VotedForIn(aa, vv, cc)
  PROVE  VotedForIn(aa, vv, cc)'
PROOF
  <1>1. PICK m \in msgs : m.type = "2b" /\ m.val = vv /\ m.bal = cc /\ m.acc = aa
    BY DEF VotedForIn
  <1>2. m \in msgs' BY <1>1
  <1> QED BY <1>1, <1>2 DEF VotedForIn

(* When the only new message is non-2b, VotedForIn doesn't gain new entries. *)
LEMMA VotedForIn_Add_Non2b ==
  ASSUME NEW aa, NEW vv, NEW cc, NEW nm,
         msgs' = msgs \cup {nm},
         nm.type # "2b",
         VotedForIn(aa, vv, cc)'
  PROVE  VotedForIn(aa, vv, cc)
PROOF
  <1>1. PICK m \in msgs' : m.type = "2b" /\ m.val = vv /\ m.bal = cc /\ m.acc = aa
    BY DEF VotedForIn
  <1>2. m \in msgs
    <2>1. m \in msgs \cup {nm} OBVIOUS
    <2>2. m # nm BY <1>1
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2 DEF VotedForIn

(* When new 2b message has parameters (a0, val0, bal0), new VotedForIn entries are only for (a0,val0,bal0). *)
LEMMA VotedForIn_Add_2b ==
  ASSUME NEW aa, NEW vv, NEW cc,
         NEW a0, NEW val0, NEW bal0,
         msgs' = msgs \cup {[type |-> "2b", bal |-> bal0, val |-> val0, acc |-> a0]},
         VotedForIn(aa, vv, cc)'
  PROVE  VotedForIn(aa, vv, cc) \/ (aa = a0 /\ vv = val0 /\ cc = bal0)
PROOF
  <1>1. PICK m \in msgs' : m.type = "2b" /\ m.val = vv /\ m.bal = cc /\ m.acc = aa
    BY DEF VotedForIn
  <1>2. m \in msgs \cup {[type |-> "2b", bal |-> bal0, val |-> val0, acc |-> a0]} OBVIOUS
  <1>3. CASE m \in msgs BY <1>1, <1>3 DEF VotedForIn
  <1>4. CASE m = [type |-> "2b", bal |-> bal0, val |-> val0, acc |-> a0] BY <1>4, <1>1
  <1> QED BY <1>2, <1>3, <1>4

LEMMA VotedForIn_New_2b ==
  ASSUME NEW a0, NEW val0, NEW bal0,
         msgs' = msgs \cup {[type |-> "2b", bal |-> bal0, val |-> val0, acc |-> a0]}
  PROVE  VotedForIn(a0, val0, bal0)'
PROOF
  <1> DEFINE nm == [type |-> "2b", bal |-> bal0, val |-> val0, acc |-> a0]
  <1>1. nm \in msgs' OBVIOUS
  <1>2. nm.type = "2b" /\ nm.val = val0 /\ nm.bal = bal0 /\ nm.acc = a0 OBVIOUS
  <1> QED BY <1>1, <1>2 DEF VotedForIn

(* At most one value is voted for in any ballot. *)
LEMMA VotedOnce ==
  ASSUME MsgInv,
         NEW a1, NEW a2, NEW vv1, NEW vv2, NEW bb,
         VotedForIn(a1, vv1, bb),
         VotedForIn(a2, vv2, bb)
  PROVE  vv1 = vv2
PROOF
  <1>1. PICK m1 \in msgs : m1.type = "2b" /\ m1.val = vv1 /\ m1.bal = bb /\ m1.acc = a1
    BY DEF VotedForIn
  <1>2. PICK m2 \in msgs : m2.type = "2b" /\ m2.val = vv2 /\ m2.bal = bb /\ m2.acc = a2
    BY DEF VotedForIn
  <1>3. PICK ma1 \in msgs : ma1.type = "2a" /\ ma1.bal = bb /\ ma1.val = vv1
    BY <1>1 DEF MsgInv
  <1>4. PICK ma2 \in msgs : ma2.type = "2a" /\ ma2.bal = bb /\ ma2.val = vv2
    BY <1>2 DEF MsgInv
  <1>5. ma2 = ma1 BY <1>3, <1>4 DEF MsgInv
  <1> QED BY <1>3, <1>4, <1>5

LEMMA InitInv == Init => Inv
PROOF
  <1> SUFFICES ASSUME Init PROVE Inv OBVIOUS
  <1>1. TypeOK
    BY NoneNotAValue DEF Init, TypeOK, Ballots, Messages
  <1>2. MsgInv
    BY DEF Init, MsgInv
  <1>3. AccInv
    <2> SUFFICES ASSUME NEW a \in Acceptors
                 PROVE  /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
                        /\ maxVBal[a] =< maxBal[a]
                        /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
                        /\ \A c \in Ballots : c > maxVBal[a] => ~ \E v \in Values : VotedForIn(a, v, c)
       BY DEF AccInv
    <2>1. maxVal[a] = None /\ maxVBal[a] = -1 /\ maxBal[a] = -1
       BY DEF Init
    <2>2. msgs = {} BY DEF Init
    <2>3. \A vv, cc : ~VotedForIn(a, vv, cc)
       BY <2>2 DEF VotedForIn
    <2> QED BY <2>1, <2>3
  <1> QED BY <1>1, <1>2, <1>3 DEF Inv

LEMMA Phase1aInv ==
  ASSUME Inv, NEW b0 \in Ballots, Phase1a(b0)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv
  <1>x. /\ msgs' = msgs \cup {[type |-> "1a", bal |-> b0]}
        /\ maxBal' = maxBal
        /\ maxVBal' = maxVBal
        /\ maxVal' = maxVal
    BY DEF Phase1a, Send
  <1>nm. [type |-> "1a", bal |-> b0].type = "1a" /\ [type |-> "1a", bal |-> b0].type # "2b"
    OBVIOUS
  <1>sub. msgs \subseteq msgs' BY <1>x
  <1>1. TypeOK'
    <2>1. [type |-> "1a", bal |-> b0] \in Messages BY DEF Messages
    <2>2. msgs' \subseteq Messages BY <1>x, <2>1 DEF TypeOK
    <2> QED BY <2>2, <1>x DEF TypeOK
  <1>2. MsgInv'
    <2> SUFFICES ASSUME NEW m \in msgs'
                 PROVE  /\ (m.type = "1b") =>
                            /\ m.bal =< maxBal[m.acc]'
                            /\ \/ /\ m.maxVal \in Values
                                  /\ m.maxVBal \in Ballots
                                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                               \/ /\ m.maxVal = None
                                  /\ m.maxVBal = -1
                            /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                  ~ \E v \in Values : VotedForIn(m.acc, v, c)'
                        /\ (m.type = "2a") =>
                              /\ SafeAt(m.val, m.bal)'
                              /\ \A ma \in msgs' :
                                   (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                        /\ (m.type = "2b") =>
                              /\ \E ma \in msgs' : /\ ma.type = "2a"
                                                   /\ ma.bal  = m.bal
                                                   /\ ma.val  = m.val
                              /\ m.bal =< maxVBal[m.acc]'
        BY DEF MsgInv
    <2>1. CASE m = [type |-> "1a", bal |-> b0]
      BY <2>1
    <2>2. CASE m \in msgs
      <3>1. ASSUME m.type = "1b"
            PROVE  /\ m.bal =< maxBal[m.acc]'
                   /\ \/ /\ m.maxVal \in Values
                         /\ m.maxVBal \in Ballots
                         /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                      \/ /\ m.maxVal = None
                         /\ m.maxVBal = -1
                   /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                         ~ \E v \in Values : VotedForIn(m.acc, v, c)'
        <4>1. /\ m.bal =< maxBal[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E v \in Values : VotedForIn(m.acc, v, c)
          BY <2>2, <3>1 DEF MsgInv
        <4>2. m.bal =< maxBal[m.acc]' BY <4>1, <1>x
        <4>3. \/ /\ m.maxVal \in Values
                 /\ m.maxVBal \in Ballots
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              \/ /\ m.maxVal = None
                 /\ m.maxVBal = -1
          <5>1. CASE /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            BY <5>1, <1>sub, VotedForIn_Mono
          <5>2. CASE m.maxVal = None /\ m.maxVBal = -1 BY <5>2
          <5> QED BY <4>1, <5>1, <5>2
        <4>4. \A c \in (m.maxVBal+1) .. (m.bal-1) :
                ~ \E v \in Values : VotedForIn(m.acc, v, c)'
          <5> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1),
                              NEW v \in Values, VotedForIn(m.acc, v, c)'
                       PROVE FALSE OBVIOUS
          <5>1. ~ \E vv \in Values : VotedForIn(m.acc, vv, c) BY <4>1
          <5>2. VotedForIn(m.acc, v, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>2, <4>3, <4>4
      <3>2. ASSUME m.type = "2a"
            PROVE  /\ SafeAt(m.val, m.bal)'
                   /\ \A ma \in msgs' :
                         (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        <4>1. SafeAt(m.val, m.bal) BY <2>2, <3>2 DEF MsgInv
        <4>2. SafeAt(m.val, m.bal)'
          <5> SUFFICES ASSUME NEW c \in 0..(m.bal-1)
                       PROVE  \E Q \in Quorums :
                                \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
              BY DEF SafeAt
          <5>1. \E Q \in Quorums :
                  \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
            BY <4>1 DEF SafeAt
          <5>2. PICK Q \in Quorums :
                  \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
            BY <5>1
          <5>3. \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
            <6> SUFFICES ASSUME NEW aa \in Q
                         PROVE  VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
                OBVIOUS
            <6>1. VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c) BY <5>2
            <6>2. CASE VotedForIn(aa, m.val, c) BY <6>2, <1>sub, VotedForIn_Mono
            <6>3. CASE WontVoteIn(aa, c)
              <7>1. \A vv \in Values : ~VotedForIn(aa, vv, c) BY <6>3 DEF WontVoteIn
              <7>2. \A vv \in Values : ~VotedForIn(aa, vv, c)'
                <8> SUFFICES ASSUME NEW vv \in Values, VotedForIn(aa, vv, c)'
                             PROVE FALSE OBVIOUS
                <8>1. VotedForIn(aa, vv, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
                <8>2. ~VotedForIn(aa, vv, c) BY <7>1
                <8> QED BY <8>1, <8>2
              <7>3. maxBal[aa] > c BY <6>3 DEF WontVoteIn
              <7>4. maxBal[aa]' > c BY <1>x, <7>3
              <7>5. WontVoteIn(aa, c)' BY <7>2, <7>4 DEF WontVoteIn
              <7> QED BY <7>5
            <6> QED BY <6>1, <6>2, <6>3
          <5> QED BY <5>3
        <4>3. \A ma \in msgs' :
                 (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
          <5> SUFFICES ASSUME NEW ma \in msgs',
                              ma.type = "2a", ma.bal = m.bal
                       PROVE  ma = m
              OBVIOUS
          <5>1. ma \in msgs
            <6>1. ma \in msgs \cup {[type |-> "1a", bal |-> b0]} BY <1>x
            <6>2. ma # [type |-> "1a", bal |-> b0] OBVIOUS
            <6> QED BY <6>1, <6>2
          <5>2. \A ma2 \in msgs :
                  (ma2.type = "2a") /\ (ma2.bal = m.bal) => (ma2 = m)
            BY <2>2, <3>2 DEF MsgInv
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>2, <4>3
      <3>3. ASSUME m.type = "2b"
            PROVE  /\ \E ma \in msgs' : /\ ma.type = "2a"
                                       /\ ma.bal  = m.bal
                                       /\ ma.val  = m.val
                   /\ m.bal =< maxVBal[m.acc]'
        <4>1. /\ \E ma \in msgs : /\ ma.type = "2a"
                                 /\ ma.bal  = m.bal
                                 /\ ma.val  = m.val
              /\ m.bal =< maxVBal[m.acc]
          BY <2>2, <3>3 DEF MsgInv
        <4>2. PICK ma \in msgs : ma.type = "2a" /\ ma.bal = m.bal /\ ma.val = m.val
          BY <4>1
        <4>3. ma \in msgs' BY <1>x, <4>2
        <4>4. m.bal =< maxVBal[m.acc]' BY <4>1, <1>x
        <4> QED BY <4>2, <4>3, <4>4
      <3> QED BY <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2, <1>x
  <1>3. AccInv'
    <2> SUFFICES ASSUME NEW a \in Acceptors
                 PROVE  /\ (maxVal[a]' = None) <=> (maxVBal[a]' = -1)
                        /\ maxVBal[a]' =< maxBal[a]'
                        /\ (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
                        /\ \A c \in Ballots : c > maxVBal[a]' =>
                                ~ \E v \in Values : VotedForIn(a, v, c)'
        BY DEF AccInv
    <2>1. /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
          /\ maxVBal[a] =< maxBal[a]
          /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
          /\ \A c \in Ballots : c > maxVBal[a] =>
                  ~ \E v \in Values : VotedForIn(a, v, c)
       BY DEF AccInv
    <2>2. (maxVal[a]' = None) <=> (maxVBal[a]' = -1) BY <2>1, <1>x
    <2>3. maxVBal[a]' =< maxBal[a]' BY <2>1, <1>x
    <2>4. (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
      <3>1. ASSUME maxVBal[a]' >= 0 PROVE VotedForIn(a, maxVal[a], maxVBal[a])'
        <4>1. maxVBal[a] >= 0 BY <3>1, <1>x
        <4>2. VotedForIn(a, maxVal[a], maxVBal[a]) BY <4>1, <2>1
        <4>3. PICK m \in msgs : m.type = "2b" /\ m.val = maxVal[a] /\ m.bal = maxVBal[a] /\ m.acc = a
              BY <4>2 DEF VotedForIn
        <4>4. m \in msgs' BY <4>3, <1>x
        <4>5. maxVal[a]' = maxVal[a] /\ maxVBal[a]' = maxVBal[a] BY <1>x
        <4> QED BY <4>3, <4>4, <4>5 DEF VotedForIn
      <3> QED BY <3>1
    <2>5. \A c \in Ballots : c > maxVBal[a]' =>
              ~ \E v \in Values : VotedForIn(a, v, c)'
      <3> SUFFICES ASSUME NEW c \in Ballots, c > maxVBal[a]',
                          NEW v \in Values, VotedForIn(a, v, c)'
                   PROVE  FALSE
          OBVIOUS
      <3>1. c > maxVBal[a] BY <1>x
      <3>2. ~ \E vv \in Values : VotedForIn(a, vv, c) BY <2>1, <3>1
      <3>3. VotedForIn(a, v, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>2, <2>3, <2>4, <2>5
  <1> QED BY <1>1, <1>2, <1>3

LEMMA Phase1bInv ==
  ASSUME Inv, NEW a0 \in Acceptors, Phase1b(a0)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv
  <1>0. PICK m0 \in msgs :
            /\ m0.type = "1a"
            /\ m0.bal > maxBal[a0]
            /\ maxBal' = [maxBal EXCEPT ![a0] = m0.bal]
            /\ Send([type |-> "1b", bal |-> m0.bal,
                  maxVBal |-> maxVBal[a0], maxVal |-> maxVal[a0], acc |-> a0])
            /\ UNCHANGED <<maxVBal, maxVal>>
    BY DEF Phase1b
  <1>tk. /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
         /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
         /\ maxVal \in [Acceptors -> Values \cup {None}]
         /\ msgs \in SUBSET Messages
    BY DEF TypeOK
  <1>m. m0 \in Messages /\ m0.bal \in Ballots
    BY <1>0, <1>tk DEF Messages
  <1>x. /\ msgs' = msgs \cup {[type |-> "1b", bal |-> m0.bal,
                                maxVBal |-> maxVBal[a0], maxVal |-> maxVal[a0], acc |-> a0]}
        /\ maxBal' = [maxBal EXCEPT ![a0] = m0.bal]
        /\ maxVBal' = maxVBal
        /\ maxVal' = maxVal
    BY <1>0 DEF Send
  <1>nm. /\ [type |-> "1b", bal |-> m0.bal,
            maxVBal |-> maxVBal[a0], maxVal |-> maxVal[a0], acc |-> a0].type = "1b"
         /\ [type |-> "1b", bal |-> m0.bal,
            maxVBal |-> maxVBal[a0], maxVal |-> maxVal[a0], acc |-> a0].type # "2b"
    OBVIOUS
  <1>sub. msgs \subseteq msgs' BY <1>x
  <1>mbge. \A a \in Acceptors : maxBal[a]' >= maxBal[a]
    <2> SUFFICES ASSUME NEW a \in Acceptors PROVE maxBal[a]' >= maxBal[a]
        OBVIOUS
    <2>1. maxBal[a] \in Ballots \cup {-1} BY <1>tk
    <2>2. CASE a = a0
      <3>1. maxBal[a]' = m0.bal BY <1>x, <2>2, <1>tk
      <3>2. maxBal[a0] < m0.bal BY <1>0
      <3>3. maxBal[a0] \in Ballots \cup {-1} BY <1>tk
      <3> QED BY <3>1, <3>2, <3>3, <1>m, <2>2 DEF Ballots
    <2>3. CASE a # a0
      <3>1. maxBal[a]' = maxBal[a] BY <1>x, <2>3, <1>tk
      <3> QED BY <3>1, <2>1 DEF Ballots
    <2> QED BY <2>2, <2>3
  <1>1. TypeOK'
    <2>1. [type |-> "1b", bal |-> m0.bal,
            maxVBal |-> maxVBal[a0], maxVal |-> maxVal[a0], acc |-> a0] \in Messages
      <3>1. maxVBal[a0] \in Ballots \cup {-1} BY <1>tk
      <3>2. maxVal[a0] \in Values \cup {None} BY <1>tk
      <3> QED BY <1>m, <3>1, <3>2 DEF Messages
    <2>2. msgs' \subseteq Messages BY <1>x, <2>1, <1>tk
    <2>3. maxBal' \in [Acceptors -> Ballots \cup {-1}] BY <1>x, <1>m, <1>tk
    <2>4. maxVBal' \in [Acceptors -> Ballots \cup {-1}] BY <1>x, <1>tk
    <2>5. maxVal' \in [Acceptors -> Values \cup {None}] BY <1>x, <1>tk
    <2>6. \A a \in Acceptors : maxBal[a]' >= maxVBal[a]'
      <3> SUFFICES ASSUME NEW a \in Acceptors PROVE maxBal[a]' >= maxVBal[a]'
          OBVIOUS
      <3>1. maxVBal[a]' = maxVBal[a] BY <1>x
      <3>2. maxBal[a]' >= maxBal[a] BY <1>mbge
      <3>3. maxBal[a] >= maxVBal[a] BY DEF TypeOK
      <3>4. maxVBal[a] \in Ballots \cup {-1} BY <1>tk
      <3>5. maxBal[a] \in Ballots \cup {-1} BY <1>tk
      <3>6. maxBal[a]' \in Ballots \cup {-1} BY <2>3
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Ballots
    <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  <1>2. MsgInv'
    <2> DEFINE newm == [type |-> "1b", bal |-> m0.bal,
                        maxVBal |-> maxVBal[a0], maxVal |-> maxVal[a0], acc |-> a0]
    <2> SUFFICES ASSUME NEW m \in msgs'
                 PROVE  /\ (m.type = "1b") =>
                            /\ m.bal =< maxBal[m.acc]'
                            /\ \/ /\ m.maxVal \in Values
                                  /\ m.maxVBal \in Ballots
                                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                               \/ /\ m.maxVal = None
                                  /\ m.maxVBal = -1
                            /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                  ~ \E v \in Values : VotedForIn(m.acc, v, c)'
                        /\ (m.type = "2a") =>
                              /\ SafeAt(m.val, m.bal)'
                              /\ \A ma \in msgs' :
                                   (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                        /\ (m.type = "2b") =>
                              /\ \E ma \in msgs' : /\ ma.type = "2a"
                                                   /\ ma.bal  = m.bal
                                                   /\ ma.val  = m.val
                              /\ m.bal =< maxVBal[m.acc]'
        BY DEF MsgInv
    <2>1. CASE m = newm
      <3>1. m.type = "1b" /\ m.acc = a0 /\ m.bal = m0.bal /\ m.maxVBal = maxVBal[a0] /\ m.maxVal = maxVal[a0]
        BY <2>1
      <3>2. maxBal[a0]' = m0.bal BY <1>x, <1>tk
      <3>3. m.bal =< maxBal[m.acc]' BY <3>1, <3>2, <1>m DEF Ballots
      <3>4. \/ /\ m.maxVal \in Values
               /\ m.maxVBal \in Ballots
               /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
            \/ /\ m.maxVal = None
               /\ m.maxVBal = -1
        <4>1. (maxVal[a0] = None) <=> (maxVBal[a0] = -1) BY DEF AccInv
        <4>2. (maxVBal[a0] >= 0) => VotedForIn(a0, maxVal[a0], maxVBal[a0]) BY DEF AccInv
        <4>3. maxVal[a0] \in Values \cup {None} BY <1>tk
        <4>4. maxVBal[a0] \in Ballots \cup {-1} BY <1>tk
        <4>5. CASE maxVBal[a0] = -1
          <5>1. maxVal[a0] = None BY <4>1, <4>5
          <5> QED BY <3>1, <4>5, <5>1
        <4>6. CASE maxVBal[a0] # -1
          <5>1. maxVBal[a0] \in Ballots BY <4>4, <4>6
          <5>2. maxVBal[a0] >= 0 BY <5>1 DEF Ballots
          <5>3. VotedForIn(a0, maxVal[a0], maxVBal[a0]) BY <4>2, <5>2
          <5>4. maxVal[a0] # None BY <4>1, <4>6
          <5>5. maxVal[a0] \in Values BY <4>3, <5>4
          <5>6. m.maxVal = maxVal[a0] /\ m.maxVBal = maxVBal[a0] /\ m.acc = a0 BY <3>1
          <5>7. m.maxVal \in Values /\ m.maxVBal \in Ballots BY <5>6, <5>1, <5>5
          <5>8. VotedForIn(m.acc, m.maxVal, m.maxVBal) BY <5>3, <5>6
          <5>9. PICK mm \in msgs : mm.type = "2b" /\ mm.val = m.maxVal /\ mm.bal = m.maxVBal /\ mm.acc = m.acc
              BY <5>8 DEF VotedForIn
          <5>10. mm \in msgs' BY <5>9, <1>sub
          <5>11. VotedForIn(m.acc, m.maxVal, m.maxVBal)' BY <5>9, <5>10 DEF VotedForIn
          <5> QED BY <5>7, <5>11
        <4> QED BY <4>5, <4>6
      <3>5. \A c \in (m.maxVBal+1) .. (m.bal-1) :
              ~ \E v \in Values : VotedForIn(m.acc, v, c)'
        <4> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1),
                            NEW v \in Values, VotedForIn(m.acc, v, c)'
                     PROVE FALSE
            OBVIOUS
        <4>1. m.maxVBal = maxVBal[a0] /\ m.bal = m0.bal /\ m.acc = a0 BY <3>1
        <4>2. maxVBal[a0] \in Ballots \cup {-1} BY <1>tk
        <4>3. c \in (maxVBal[a0]+1)..(m0.bal-1) BY <4>1
        <4>4. c > maxVBal[a0]
          <5>1. c >= maxVBal[a0]+1 BY <4>3, <4>2, <1>m DEF Ballots
          <5> QED BY <5>1, <4>2 DEF Ballots
        <4>5. c \in Ballots
          <5>1. c >= 0 BY <4>3, <4>2 DEF Ballots
          <5>2. c <= m0.bal - 1 BY <4>3, <4>2, <1>m DEF Ballots
          <5>3. c \in Int BY <4>3, <4>2, <1>m DEF Ballots
          <5> QED BY <5>1, <5>3 DEF Ballots
        <4>6. \A vv \in Values : ~VotedForIn(a0, vv, c) BY <4>4, <4>5 DEF AccInv
        <4>7. VotedForIn(a0, v, c) BY <4>1, <1>x, <1>nm, VotedForIn_Add_Non2b
        <4> QED BY <4>6, <4>7
      <3> QED BY <3>1, <3>3, <3>4, <3>5
    <2>2. CASE m \in msgs
      <3>m_type. m \in Messages BY <2>2, <1>tk
      <3>1. ASSUME m.type = "1b"
            PROVE  /\ m.bal =< maxBal[m.acc]'
                   /\ \/ /\ m.maxVal \in Values
                         /\ m.maxVBal \in Ballots
                         /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                      \/ /\ m.maxVal = None
                         /\ m.maxVBal = -1
                   /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                         ~ \E v \in Values : VotedForIn(m.acc, v, c)'
        <4>m_field. m.acc \in Acceptors /\ m.bal \in Ballots
          BY <3>m_type, <3>1 DEF Messages
        <4>1. /\ m.bal =< maxBal[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E v \in Values : VotedForIn(m.acc, v, c)
          BY <2>2, <3>1 DEF MsgInv
        <4>2. m.bal =< maxBal[m.acc]'
          <5>1. maxBal[m.acc]' >= maxBal[m.acc] BY <1>mbge, <4>m_field
          <5>2. m.bal =< maxBal[m.acc] BY <4>1
          <5>3. maxBal[m.acc] \in Ballots \cup {-1} BY <1>tk, <4>m_field
          <5>4. maxBal[m.acc]' \in Ballots \cup {-1}
            <6>1. maxBal' \in [Acceptors -> Ballots \cup {-1}] BY <1>1 DEF TypeOK
            <6> QED BY <6>1, <4>m_field
          <5> QED BY <5>1, <5>2, <5>3, <5>4, <4>m_field DEF Ballots
        <4>3. \/ /\ m.maxVal \in Values
                 /\ m.maxVBal \in Ballots
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              \/ /\ m.maxVal = None
                 /\ m.maxVBal = -1
          <5>1. CASE /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            <6>1. PICK mm \in msgs : mm.type = "2b" /\ mm.val = m.maxVal /\ mm.bal = m.maxVBal /\ mm.acc = m.acc
                BY <5>1 DEF VotedForIn
            <6>2. mm \in msgs' BY <6>1, <1>sub
            <6>3. VotedForIn(m.acc, m.maxVal, m.maxVBal)' BY <6>1, <6>2 DEF VotedForIn
            <6> QED BY <5>1, <6>3
          <5>2. CASE m.maxVal = None /\ m.maxVBal = -1 BY <5>2
          <5> QED BY <4>1, <5>1, <5>2
        <4>4. \A c \in (m.maxVBal+1) .. (m.bal-1) :
                ~ \E v \in Values : VotedForIn(m.acc, v, c)'
          <5> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1),
                              NEW v \in Values, VotedForIn(m.acc, v, c)'
                       PROVE FALSE OBVIOUS
          <5>1. ~ \E vv \in Values : VotedForIn(m.acc, vv, c) BY <4>1
          <5>2. VotedForIn(m.acc, v, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>2, <4>3, <4>4
      <3>2. ASSUME m.type = "2a"
            PROVE  /\ SafeAt(m.val, m.bal)'
                   /\ \A ma \in msgs' :
                        (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        <4>1. SafeAt(m.val, m.bal) BY <2>2, <3>2 DEF MsgInv
        <4>2. SafeAt(m.val, m.bal)'
          <5> SUFFICES ASSUME NEW c \in 0..(m.bal-1)
                       PROVE  \E Q \in Quorums :
                                \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
              BY DEF SafeAt
          <5>1. \E Q \in Quorums :
                  \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
            BY <4>1 DEF SafeAt
          <5>2. PICK Q \in Quorums :
                  \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
            BY <5>1
          <5>3. \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
            <6> SUFFICES ASSUME NEW aa \in Q
                         PROVE  VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
                OBVIOUS
            <6>0. aa \in Acceptors BY QuorumAssumption
            <6>1. VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c) BY <5>2
            <6>2. CASE VotedForIn(aa, m.val, c) BY <6>2, <1>sub, VotedForIn_Mono
            <6>3. CASE WontVoteIn(aa, c)
              <7>1. \A vv \in Values : ~VotedForIn(aa, vv, c) BY <6>3 DEF WontVoteIn
              <7>2. \A vv \in Values : ~VotedForIn(aa, vv, c)'
                <8> SUFFICES ASSUME NEW vv \in Values, VotedForIn(aa, vv, c)'
                             PROVE FALSE OBVIOUS
                <8>1. VotedForIn(aa, vv, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
                <8>2. ~VotedForIn(aa, vv, c) BY <7>1
                <8> QED BY <8>1, <8>2
              <7>3. maxBal[aa] > c BY <6>3 DEF WontVoteIn
              <7>4. maxBal[aa]' >= maxBal[aa] BY <1>mbge, <6>0
              <7>5. maxBal[aa] \in Ballots \cup {-1} BY <1>tk, <6>0
              <7>6. maxBal[aa]' \in Ballots \cup {-1}
                <8>1. maxBal' \in [Acceptors -> Ballots \cup {-1}] BY <1>1 DEF TypeOK
                <8> QED BY <8>1, <6>0
              <7>7. maxBal[aa]' > c BY <7>3, <7>4, <7>5, <7>6 DEF Ballots
              <7>8. WontVoteIn(aa, c)' BY <7>2, <7>7 DEF WontVoteIn
              <7> QED BY <7>8
            <6> QED BY <6>1, <6>2, <6>3
          <5> QED BY <5>3
        <4>3. \A ma \in msgs' :
                 (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
          <5> SUFFICES ASSUME NEW ma \in msgs',
                              ma.type = "2a", ma.bal = m.bal
                       PROVE  ma = m
              OBVIOUS
          <5>1. ma \in msgs
            <6>1. ma \in msgs \cup {newm} BY <1>x
            <6>2. ma # newm OBVIOUS
            <6> QED BY <6>1, <6>2
          <5>2. \A ma2 \in msgs :
                  (ma2.type = "2a") /\ (ma2.bal = m.bal) => (ma2 = m)
            BY <2>2, <3>2 DEF MsgInv
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>2, <4>3
      <3>3. ASSUME m.type = "2b"
            PROVE  /\ \E ma \in msgs' : /\ ma.type = "2a"
                                       /\ ma.bal  = m.bal
                                       /\ ma.val  = m.val
                   /\ m.bal =< maxVBal[m.acc]'
        <4>1. /\ \E ma \in msgs : /\ ma.type = "2a"
                                 /\ ma.bal  = m.bal
                                 /\ ma.val  = m.val
              /\ m.bal =< maxVBal[m.acc]
          BY <2>2, <3>3 DEF MsgInv
        <4>2. PICK ma \in msgs : ma.type = "2a" /\ ma.bal = m.bal /\ ma.val = m.val
          BY <4>1
        <4>3. ma \in msgs' BY <1>x, <4>2
        <4>4. m.bal =< maxVBal[m.acc]' BY <4>1, <1>x
        <4> QED BY <4>2, <4>3, <4>4
      <3> QED BY <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2, <1>x
  <1>3. AccInv'
    <2> SUFFICES ASSUME NEW a \in Acceptors
                 PROVE  /\ (maxVal[a]' = None) <=> (maxVBal[a]' = -1)
                        /\ maxVBal[a]' =< maxBal[a]'
                        /\ (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
                        /\ \A c \in Ballots : c > maxVBal[a]' =>
                                ~ \E v \in Values : VotedForIn(a, v, c)'
        BY DEF AccInv
    <2>1. /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
          /\ maxVBal[a] =< maxBal[a]
          /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
          /\ \A c \in Ballots : c > maxVBal[a] =>
                  ~ \E v \in Values : VotedForIn(a, v, c)
       BY DEF AccInv
    <2>2. (maxVal[a]' = None) <=> (maxVBal[a]' = -1) BY <2>1, <1>x
    <2>3. maxVBal[a]' =< maxBal[a]'
      <3>1. maxVBal[a]' = maxVBal[a] BY <1>x
      <3>2. maxBal[a]' >= maxBal[a] BY <1>mbge
      <3>3. maxBal[a] >= maxVBal[a] BY <2>1
      <3>4. maxVBal[a] \in Ballots \cup {-1} BY <1>tk
      <3>5. maxBal[a] \in Ballots \cup {-1} BY <1>tk
      <3>6. maxBal[a]' \in Ballots \cup {-1}
        <4>1. maxBal' \in [Acceptors -> Ballots \cup {-1}] BY <1>1 DEF TypeOK
        <4> QED BY <4>1
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Ballots
    <2>4. (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
      <3>1. ASSUME maxVBal[a]' >= 0 PROVE VotedForIn(a, maxVal[a], maxVBal[a])'
        <4>1. maxVBal[a] >= 0 BY <3>1, <1>x
        <4>2. VotedForIn(a, maxVal[a], maxVBal[a]) BY <4>1, <2>1
        <4>3. PICK mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a] /\ mm.bal = maxVBal[a] /\ mm.acc = a
              BY <4>2 DEF VotedForIn
        <4>4. mm \in msgs' BY <4>3, <1>sub
        <4>5. maxVal[a]' = maxVal[a] /\ maxVBal[a]' = maxVBal[a] BY <1>x
        <4> QED BY <4>3, <4>4, <4>5 DEF VotedForIn
      <3> QED BY <3>1
    <2>5. \A c \in Ballots : c > maxVBal[a]' =>
              ~ \E v \in Values : VotedForIn(a, v, c)'
      <3> SUFFICES ASSUME NEW c \in Ballots, c > maxVBal[a]',
                          NEW v \in Values, VotedForIn(a, v, c)'
                   PROVE  FALSE
          OBVIOUS
      <3>1. c > maxVBal[a] BY <1>x
      <3>2. ~ \E vv \in Values : VotedForIn(a, vv, c) BY <2>1, <3>1
      <3>3. VotedForIn(a, v, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>2, <2>3, <2>4, <2>5
  <1> QED BY <1>1, <1>2, <1>3

LEMMA Phase2aInv ==
  ASSUME Inv, NEW b0 \in Ballots, Phase2a(b0)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv
  <1>tk. /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
         /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
         /\ maxVal \in [Acceptors -> Values \cup {None}]
         /\ msgs \in SUBSET Messages
    BY DEF TypeOK
  <1>0a. ~ \E mm \in msgs : (mm.type = "2a") /\ (mm.bal = b0)
    BY DEF Phase2a
  <1>0. PICK v0 \in Values, Q0 \in Quorums,
              S0 \in SUBSET {mm \in msgs : (mm.type = "1b") /\ (mm.bal = b0)} :
            /\ \A a \in Q0 : \E m \in S0 : m.acc = a
            /\ \/ \A m \in S0 : m.maxVBal = -1
               \/ \E c \in 0..(b0-1) :
                     /\ \A m \in S0 : m.maxVBal =< c
                     /\ \E m \in S0 : /\ m.maxVBal = c
                                      /\ m.maxVal = v0
            /\ Send([type |-> "2a", bal |-> b0, val |-> v0])
    BY DEF Phase2a
  <1>x. /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b0, val |-> v0]}
        /\ maxBal' = maxBal
        /\ maxVBal' = maxVBal
        /\ maxVal' = maxVal
    BY <1>0 DEF Send, Phase2a
  <1>nm. /\ [type |-> "2a", bal |-> b0, val |-> v0].type = "2a"
         /\ [type |-> "2a", bal |-> b0, val |-> v0].type # "2b"
         /\ [type |-> "2a", bal |-> b0, val |-> v0].bal = b0
         /\ [type |-> "2a", bal |-> b0, val |-> v0].val = v0
    OBVIOUS
  <1>sub. msgs \subseteq msgs' BY <1>x
  <1>1. TypeOK'
    <2>1. [type |-> "2a", bal |-> b0, val |-> v0] \in Messages BY DEF Messages
    <2>2. msgs' \subseteq Messages BY <1>x, <2>1, <1>tk
    <2> QED BY <2>2, <1>x, <1>tk DEF TypeOK
  <1>S_props. \A m \in S0 : /\ m \in msgs
                           /\ m.type = "1b"
                           /\ m.bal = b0
                           /\ m \in Messages
                           /\ m.acc \in Acceptors
                           /\ m.maxVBal \in Ballots \cup {-1}
                           /\ m.maxVal \in Values \cup {None}
    <2> SUFFICES ASSUME NEW m \in S0
                 PROVE  /\ m \in msgs
                        /\ m.type = "1b"
                        /\ m.bal = b0
                        /\ m \in Messages
                        /\ m.acc \in Acceptors
                        /\ m.maxVBal \in Ballots \cup {-1}
                        /\ m.maxVal \in Values \cup {None}
        OBVIOUS
    <2>1. m \in msgs /\ m.type = "1b" /\ m.bal = b0 BY <1>0
    <2>2. m \in Messages BY <2>1, <1>tk
    <2> QED BY <2>1, <2>2 DEF Messages
  <1>S_msginv. \A m \in S0 :
       /\ m.bal =< maxBal[m.acc]
       /\ \/ /\ m.maxVal \in Values
             /\ m.maxVBal \in Ballots
             /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
          \/ /\ m.maxVal = None
             /\ m.maxVBal = -1
       /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
              ~ \E v \in Values : VotedForIn(m.acc, v, c)
    <2> SUFFICES ASSUME NEW m \in S0
                 PROVE  /\ m.bal =< maxBal[m.acc]
                        /\ \/ /\ m.maxVal \in Values
                              /\ m.maxVBal \in Ballots
                              /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                           \/ /\ m.maxVal = None
                              /\ m.maxVBal = -1
                        /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                              ~ \E v \in Values : VotedForIn(m.acc, v, c)
        OBVIOUS
    <2>1. m \in msgs /\ m.type = "1b" BY <1>S_props
    <2> QED BY <2>1 DEF MsgInv
  <1>safe. SafeAt(v0, b0)
    <2> SUFFICES ASSUME NEW d \in 0..(b0-1)
                 PROVE  \E Q \in Quorums :
                          \A a \in Q : VotedForIn(a, v0, d) \/ WontVoteIn(a, d)
        BY DEF SafeAt
    <2>d. d \in Nat /\ d >= 0 /\ d <= b0-1 /\ d < b0 /\ d \in Ballots
      BY DEF Ballots
    <2>1. CASE \A m \in S0 : m.maxVBal = -1
      <3>1. WITNESS Q0 \in Quorums
      <3>2. \A a \in Q0 : VotedForIn(a, v0, d) \/ WontVoteIn(a, d)
        <4> SUFFICES ASSUME NEW a \in Q0
                     PROVE  VotedForIn(a, v0, d) \/ WontVoteIn(a, d)
            OBVIOUS
        <4>0. a \in Acceptors BY QuorumAssumption
        <4>1. PICK m \in S0 : m.acc = a BY <1>0
        <4>2. m.maxVBal = -1 BY <2>1
        <4>3. m.bal = b0 BY <1>S_props
        <4>4. m.bal =< maxBal[m.acc] BY <1>S_msginv
        <4>5. d \in (m.maxVBal+1) .. (m.bal-1) BY <4>2, <4>3, <2>d DEF Ballots
        <4>6. ~ \E v \in Values : VotedForIn(m.acc, v, d) BY <1>S_msginv, <4>5
        <4>7. ~ \E v \in Values : VotedForIn(a, v, d) BY <4>1, <4>6
        <4>8. maxBal[a] >= b0
          <5>1. b0 \in Ballots OBVIOUS
          <5>2. m.bal =< maxBal[a] BY <4>4, <4>1
          <5> QED BY <5>2, <4>3
        <4>9. maxBal[a] > d
          <5>1. maxBal[a] \in Ballots \cup {-1} BY <1>tk, <4>0
          <5> QED BY <4>8, <5>1, <2>d DEF Ballots
        <4>10. WontVoteIn(a, d) BY <4>7, <4>9 DEF WontVoteIn
        <4> QED BY <4>10
      <3> QED BY <3>2
    <2>2. CASE \E c \in 0..(b0-1) :
                  /\ \A m \in S0 : m.maxVBal =< c
                  /\ \E m \in S0 : /\ m.maxVBal = c
                                   /\ m.maxVal = v0
      <3>0. PICK cc \in 0..(b0-1) : /\ \A m \in S0 : m.maxVBal =< cc
                                    /\ \E m \in S0 : /\ m.maxVBal = cc
                                                     /\ m.maxVal = v0
        BY <2>2
      <3>cc. cc \in Nat /\ cc >= 0 /\ cc <= b0-1 /\ cc < b0 /\ cc \in Ballots
        BY DEF Ballots
      <3>w. PICK mw \in S0 : mw.maxVBal = cc /\ mw.maxVal = v0 BY <3>0
      <3>wa. /\ mw.acc \in Acceptors
             /\ mw.maxVal = v0
             /\ mw.maxVBal = cc
             /\ VotedForIn(mw.acc, v0, cc)
        <4>1. mw.acc \in Acceptors BY <1>S_props
        <4>2. v0 \in Values OBVIOUS
        <4>3. /\ mw.maxVal \in Values
              /\ mw.maxVBal \in Ballots
              /\ VotedForIn(mw.acc, mw.maxVal, mw.maxVBal)
           \/ /\ mw.maxVal = None
              /\ mw.maxVBal = -1
          BY <1>S_msginv
        <4>4. mw.maxVal \in Values BY <3>w, <4>2
        <4>5. ~ (mw.maxVal = None) BY <4>4, NoneNotAValue
        <4>6. /\ mw.maxVal \in Values
              /\ mw.maxVBal \in Ballots
              /\ VotedForIn(mw.acc, mw.maxVal, mw.maxVBal)
          BY <4>3, <4>5
        <4>7. VotedForIn(mw.acc, v0, cc) BY <4>6, <3>w
        <4> QED BY <4>1, <3>w, <4>7
      <3>case1. CASE d > cc
        <4>1. WITNESS Q0 \in Quorums
        <4>2. \A a \in Q0 : VotedForIn(a, v0, d) \/ WontVoteIn(a, d)
          <5> SUFFICES ASSUME NEW a \in Q0
                       PROVE  VotedForIn(a, v0, d) \/ WontVoteIn(a, d)
              OBVIOUS
          <5>0. a \in Acceptors BY QuorumAssumption
          <5>1. PICK m \in S0 : m.acc = a BY <1>0
          <5>2. m.maxVBal =< cc BY <3>0
          <5>3. m.maxVBal \in Ballots \cup {-1} BY <1>S_props
          <5>4. m.bal = b0 BY <1>S_props
          <5>5. m.bal =< maxBal[m.acc] BY <1>S_msginv
          <5>6. d \in (m.maxVBal+1)..(m.bal-1)
            <6>1. d > cc /\ cc >= m.maxVBal BY <3>case1, <5>2
            <6>2. d > m.maxVBal BY <6>1, <5>3, <3>cc DEF Ballots
            <6>3. d >= m.maxVBal + 1 BY <6>2, <5>3, <2>d DEF Ballots
            <6>4. d <= m.bal - 1 BY <5>4, <2>d DEF Ballots
            <6>5. m.maxVBal+1 \in Int BY <5>3 DEF Ballots
            <6>6. m.bal-1 \in Int BY <5>4 DEF Ballots
            <6> QED BY <6>3, <6>4, <6>5, <6>6, <2>d DEF Ballots
          <5>7. ~ \E v \in Values : VotedForIn(m.acc, v, d) BY <1>S_msginv, <5>6
          <5>8. ~ \E v \in Values : VotedForIn(a, v, d) BY <5>1, <5>7
          <5>9. m.bal =< maxBal[a] BY <5>5, <5>1
          <5>10. maxBal[a] > d
            <6>1. maxBal[a] \in Ballots \cup {-1} BY <1>tk, <5>0
            <6>2. b0 =< maxBal[a] BY <5>4, <5>9
            <6> QED BY <6>1, <6>2, <2>d DEF Ballots
          <5>11. WontVoteIn(a, d) BY <5>8, <5>10 DEF WontVoteIn
          <5> QED BY <5>11
        <4> QED BY <4>2
      <3>case2. CASE d = cc
        <4>1. WITNESS Q0 \in Quorums
        <4>2. \A a \in Q0 : VotedForIn(a, v0, d) \/ WontVoteIn(a, d)
          <5> SUFFICES ASSUME NEW a \in Q0
                       PROVE  VotedForIn(a, v0, d) \/ WontVoteIn(a, d)
              OBVIOUS
          <5>0. a \in Acceptors BY QuorumAssumption
          <5>1. PICK m \in S0 : m.acc = a BY <1>0
          <5>2. m.maxVBal =< cc BY <3>0
          <5>3. m.maxVBal \in Ballots \cup {-1} BY <1>S_props
          <5>4. m.bal = b0 BY <1>S_props
          <5>5. m.bal =< maxBal[m.acc] BY <1>S_msginv
          <5>case_mvb_eq. CASE m.maxVBal = cc
            <6>1. /\ m.maxVal \in Values
                  /\ m.maxVBal \in Ballots
                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
               \/ /\ m.maxVal = None
                  /\ m.maxVBal = -1
              BY <1>S_msginv
            <6>2. ~ (m.maxVBal = -1) BY <5>case_mvb_eq, <3>cc DEF Ballots
            <6>3. /\ m.maxVal \in Values
                  /\ m.maxVBal \in Ballots
                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
              BY <6>1, <6>2
            <6>4. VotedForIn(m.acc, m.maxVal, cc) BY <6>3, <5>case_mvb_eq
            <6>5. VotedForIn(mw.acc, v0, cc) BY <3>wa
            <6>6. m.maxVal = v0
              <7>1. m.maxVal \in Values BY <6>3
              <7> QED BY <6>4, <6>5, <7>1, VotedOnce
            <6>7. VotedForIn(m.acc, v0, cc) BY <6>4, <6>6
            <6>8. VotedForIn(a, v0, cc) BY <6>7, <5>1
            <6>9. VotedForIn(a, v0, d) BY <6>8, <3>case2
            <6> QED BY <6>9
          <5>case_mvb_lt. CASE m.maxVBal # cc
            <6>1. m.maxVBal < cc
              <7>1. m.maxVBal =< cc BY <5>2
              <7> QED BY <7>1, <5>case_mvb_lt, <5>3, <3>cc DEF Ballots
            <6>2. d > m.maxVBal BY <6>1, <3>case2
            <6>3. d \in (m.maxVBal+1)..(m.bal-1)
              <7>1. d >= m.maxVBal + 1 BY <6>2, <5>3, <2>d DEF Ballots
              <7>2. d <= m.bal - 1 BY <5>4, <2>d DEF Ballots
              <7>3. m.maxVBal+1 \in Int BY <5>3 DEF Ballots
              <7>4. m.bal-1 \in Int BY <5>4 DEF Ballots
              <7> QED BY <7>1, <7>2, <7>3, <7>4, <2>d DEF Ballots
            <6>4. ~ \E v \in Values : VotedForIn(m.acc, v, d) BY <1>S_msginv, <6>3
            <6>5. ~ \E v \in Values : VotedForIn(a, v, d) BY <5>1, <6>4
            <6>6. m.bal =< maxBal[a] BY <5>5, <5>1
            <6>7. maxBal[a] > d
              <7>1. maxBal[a] \in Ballots \cup {-1} BY <1>tk, <5>0
              <7>2. b0 =< maxBal[a] BY <5>4, <6>6
              <7> QED BY <7>1, <7>2, <2>d DEF Ballots
            <6>8. WontVoteIn(a, d) BY <6>5, <6>7 DEF WontVoteIn
            <6> QED BY <6>8
          <5> QED BY <5>case_mvb_eq, <5>case_mvb_lt
        <4> QED BY <4>2
      <3>case3. CASE d < cc
        <4>1. VotedForIn(mw.acc, v0, cc) BY <3>wa
        <4>2. PICK m_2b \in msgs : m_2b.type = "2b" /\ m_2b.val = v0 /\ m_2b.bal = cc /\ m_2b.acc = mw.acc
          BY <4>1 DEF VotedForIn
        <4>3. PICK m_2a \in msgs : m_2a.type = "2a" /\ m_2a.bal = cc /\ m_2a.val = v0
          BY <4>2 DEF MsgInv
        <4>4. SafeAt(v0, cc) BY <4>3 DEF MsgInv
        <4>5. d \in 0..(cc-1)
          <5>1. d >= 0 BY <2>d
          <5>2. d <= cc - 1 BY <3>case3, <3>cc, <2>d DEF Ballots
          <5>3. d \in Int BY <2>d DEF Ballots
          <5>4. cc - 1 \in Int BY <3>cc DEF Ballots
          <5> QED BY <5>1, <5>2, <5>3, <5>4
        <4>6. \E Q \in Quorums :
                \A a \in Q : VotedForIn(a, v0, d) \/ WontVoteIn(a, d)
          BY <4>4, <4>5 DEF SafeAt
        <4> QED BY <4>6
      <3> QED BY <3>case1, <3>case2, <3>case3, <2>d, <3>cc DEF Ballots
    <2> QED BY <1>0, <2>1, <2>2
  <1>2. MsgInv'
    <2> DEFINE newm2a == [type |-> "2a", bal |-> b0, val |-> v0]
    <2> SUFFICES ASSUME NEW m \in msgs'
                 PROVE  /\ (m.type = "1b") =>
                            /\ m.bal =< maxBal[m.acc]'
                            /\ \/ /\ m.maxVal \in Values
                                  /\ m.maxVBal \in Ballots
                                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                               \/ /\ m.maxVal = None
                                  /\ m.maxVBal = -1
                            /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                  ~ \E v \in Values : VotedForIn(m.acc, v, c)'
                        /\ (m.type = "2a") =>
                              /\ SafeAt(m.val, m.bal)'
                              /\ \A ma \in msgs' :
                                   (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                        /\ (m.type = "2b") =>
                              /\ \E ma \in msgs' : /\ ma.type = "2a"
                                                   /\ ma.bal  = m.bal
                                                   /\ ma.val  = m.val
                              /\ m.bal =< maxVBal[m.acc]'
        BY DEF MsgInv
    <2>1. CASE m = newm2a
      <3>1. m.type = "2a" /\ m.val = v0 /\ m.bal = b0 BY <2>1
      <3>2. SafeAt(m.val, m.bal)'
        <4>1. SafeAt(v0, b0) BY <1>safe
        <4>2. SafeAt(m.val, m.bal) BY <4>1, <3>1
        <4> SUFFICES ASSUME NEW c \in 0..(m.bal-1)
                     PROVE  \E Q \in Quorums :
                              \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
            BY DEF SafeAt
        <4>3. \E Q \in Quorums :
                \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
          BY <4>2 DEF SafeAt
        <4>4. PICK Q \in Quorums :
                \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
          BY <4>3
        <4>5. \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
          <5> SUFFICES ASSUME NEW aa \in Q
                       PROVE  VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
              OBVIOUS
          <5>1. VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c) BY <4>4
          <5>2. CASE VotedForIn(aa, m.val, c) BY <5>2, <1>sub, VotedForIn_Mono
          <5>3. CASE WontVoteIn(aa, c)
            <6>1. \A vv \in Values : ~VotedForIn(aa, vv, c) BY <5>3 DEF WontVoteIn
            <6>2. \A vv \in Values : ~VotedForIn(aa, vv, c)'
              <7> SUFFICES ASSUME NEW vv \in Values, VotedForIn(aa, vv, c)'
                           PROVE FALSE OBVIOUS
              <7>1. VotedForIn(aa, vv, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
              <7> QED BY <7>1, <6>1
            <6>3. maxBal[aa] > c BY <5>3 DEF WontVoteIn
            <6>4. maxBal[aa]' > c BY <1>x, <6>3
            <6> QED BY <6>2, <6>4 DEF WontVoteIn
          <5> QED BY <5>1, <5>2, <5>3
        <4> QED BY <4>5
      <3>3. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        <4> SUFFICES ASSUME NEW ma \in msgs', ma.type = "2a", ma.bal = m.bal
                     PROVE  ma = m
            OBVIOUS
        <4>1. ma.bal = b0 BY <3>1
        <4>2. ma \in msgs \cup {newm2a} BY <1>x
        <4>3. CASE ma \in msgs
          <5>1. ~ \E mma \in msgs : (mma.type = "2a") /\ (mma.bal = b0) BY <1>0a
          <5> QED BY <4>3, <4>1, <5>1
        <4>4. CASE ma = newm2a BY <4>4, <2>1
        <4> QED BY <4>2, <4>3, <4>4
      <3> QED BY <3>1, <3>2, <3>3
    <2>2. CASE m \in msgs
      <3>m_type. m \in Messages BY <2>2, <1>tk
      <3>1. ASSUME m.type = "1b"
            PROVE  /\ m.bal =< maxBal[m.acc]'
                   /\ \/ /\ m.maxVal \in Values
                         /\ m.maxVBal \in Ballots
                         /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                      \/ /\ m.maxVal = None
                         /\ m.maxVBal = -1
                   /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                         ~ \E v \in Values : VotedForIn(m.acc, v, c)'
        <4>1. /\ m.bal =< maxBal[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E v \in Values : VotedForIn(m.acc, v, c)
          BY <2>2, <3>1 DEF MsgInv
        <4>2. m.bal =< maxBal[m.acc]' BY <4>1, <1>x
        <4>3. \/ /\ m.maxVal \in Values
                 /\ m.maxVBal \in Ballots
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              \/ /\ m.maxVal = None
                 /\ m.maxVBal = -1
          <5>1. CASE /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            <6>1. PICK mm \in msgs : mm.type = "2b" /\ mm.val = m.maxVal /\ mm.bal = m.maxVBal /\ mm.acc = m.acc
                BY <5>1 DEF VotedForIn
            <6>2. mm \in msgs' BY <6>1, <1>sub
            <6> QED BY <5>1, <6>1, <6>2 DEF VotedForIn
          <5>2. CASE m.maxVal = None /\ m.maxVBal = -1 BY <5>2
          <5> QED BY <4>1, <5>1, <5>2
        <4>4. \A c \in (m.maxVBal+1) .. (m.bal-1) :
                ~ \E v \in Values : VotedForIn(m.acc, v, c)'
          <5> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1),
                              NEW v \in Values, VotedForIn(m.acc, v, c)'
                       PROVE FALSE OBVIOUS
          <5>1. ~ \E vv \in Values : VotedForIn(m.acc, vv, c) BY <4>1
          <5>2. VotedForIn(m.acc, v, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>2, <4>3, <4>4
      <3>2. ASSUME m.type = "2a"
            PROVE  /\ SafeAt(m.val, m.bal)'
                   /\ \A ma \in msgs' :
                         (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        <4>1. SafeAt(m.val, m.bal) BY <2>2, <3>2 DEF MsgInv
        <4>2. SafeAt(m.val, m.bal)'
          <5> SUFFICES ASSUME NEW c \in 0..(m.bal-1)
                       PROVE  \E Q \in Quorums :
                                \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
              BY DEF SafeAt
          <5>1. \E Q \in Quorums :
                  \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
            BY <4>1 DEF SafeAt
          <5>2. PICK Q \in Quorums :
                  \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
            BY <5>1
          <5>3. \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
            <6> SUFFICES ASSUME NEW aa \in Q
                         PROVE  VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
                OBVIOUS
            <6>1. VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c) BY <5>2
            <6>2. CASE VotedForIn(aa, m.val, c) BY <6>2, <1>sub, VotedForIn_Mono
            <6>3. CASE WontVoteIn(aa, c)
              <7>1. \A vv \in Values : ~VotedForIn(aa, vv, c) BY <6>3 DEF WontVoteIn
              <7>2. \A vv \in Values : ~VotedForIn(aa, vv, c)'
                <8> SUFFICES ASSUME NEW vv \in Values, VotedForIn(aa, vv, c)'
                             PROVE FALSE OBVIOUS
                <8>1. VotedForIn(aa, vv, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
                <8> QED BY <8>1, <7>1
              <7>3. maxBal[aa] > c BY <6>3 DEF WontVoteIn
              <7>4. maxBal[aa]' > c BY <1>x, <7>3
              <7> QED BY <7>2, <7>4 DEF WontVoteIn
            <6> QED BY <6>1, <6>2, <6>3
          <5> QED BY <5>3
        <4>3. \A ma \in msgs' :
                 (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
          <5> SUFFICES ASSUME NEW ma \in msgs',
                              ma.type = "2a", ma.bal = m.bal
                       PROVE  ma = m
              OBVIOUS
          <5>1. ma \in msgs \cup {newm2a} BY <1>x
          <5>2. CASE ma \in msgs
            <6>1. \A ma2 \in msgs :
                    (ma2.type = "2a") /\ (ma2.bal = m.bal) => (ma2 = m)
              BY <2>2, <3>2 DEF MsgInv
            <6> QED BY <5>2, <6>1
          <5>3. CASE ma = newm2a
            <6>1. ma.bal = b0 BY <5>3
            <6>2. m.bal = b0 BY <6>1
            <6>3. ~ \E mma \in msgs : (mma.type = "2a") /\ (mma.bal = b0) BY <1>0a
            <6> QED BY <2>2, <3>2, <6>2, <6>3
          <5> QED BY <5>1, <5>2, <5>3
        <4> QED BY <4>2, <4>3
      <3>3. ASSUME m.type = "2b"
            PROVE  /\ \E ma \in msgs' : /\ ma.type = "2a"
                                       /\ ma.bal  = m.bal
                                       /\ ma.val  = m.val
                   /\ m.bal =< maxVBal[m.acc]'
        <4>1. /\ \E ma \in msgs : /\ ma.type = "2a"
                                 /\ ma.bal  = m.bal
                                 /\ ma.val  = m.val
              /\ m.bal =< maxVBal[m.acc]
          BY <2>2, <3>3 DEF MsgInv
        <4>2. PICK ma \in msgs : ma.type = "2a" /\ ma.bal = m.bal /\ ma.val = m.val
          BY <4>1
        <4>3. ma \in msgs' BY <1>x, <4>2
        <4>4. m.bal =< maxVBal[m.acc]' BY <4>1, <1>x
        <4> QED BY <4>2, <4>3, <4>4
      <3> QED BY <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2, <1>x
  <1>3. AccInv'
    <2> SUFFICES ASSUME NEW a \in Acceptors
                 PROVE  /\ (maxVal[a]' = None) <=> (maxVBal[a]' = -1)
                        /\ maxVBal[a]' =< maxBal[a]'
                        /\ (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
                        /\ \A c \in Ballots : c > maxVBal[a]' =>
                                ~ \E v \in Values : VotedForIn(a, v, c)'
        BY DEF AccInv
    <2>1. /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
          /\ maxVBal[a] =< maxBal[a]
          /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
          /\ \A c \in Ballots : c > maxVBal[a] =>
                  ~ \E v \in Values : VotedForIn(a, v, c)
       BY DEF AccInv
    <2>2. (maxVal[a]' = None) <=> (maxVBal[a]' = -1) BY <2>1, <1>x
    <2>3. maxVBal[a]' =< maxBal[a]' BY <2>1, <1>x
    <2>4. (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
      <3>1. ASSUME maxVBal[a]' >= 0 PROVE VotedForIn(a, maxVal[a], maxVBal[a])'
        <4>1. maxVBal[a] >= 0 BY <3>1, <1>x
        <4>2. VotedForIn(a, maxVal[a], maxVBal[a]) BY <4>1, <2>1
        <4>3. PICK mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a] /\ mm.bal = maxVBal[a] /\ mm.acc = a
              BY <4>2 DEF VotedForIn
        <4>4. mm \in msgs' BY <4>3, <1>sub
        <4>5. maxVal[a]' = maxVal[a] /\ maxVBal[a]' = maxVBal[a] BY <1>x
        <4> QED BY <4>3, <4>4, <4>5 DEF VotedForIn
      <3> QED BY <3>1
    <2>5. \A c \in Ballots : c > maxVBal[a]' =>
              ~ \E v \in Values : VotedForIn(a, v, c)'
      <3> SUFFICES ASSUME NEW c \in Ballots, c > maxVBal[a]',
                          NEW v \in Values, VotedForIn(a, v, c)'
                   PROVE  FALSE
          OBVIOUS
      <3>1. c > maxVBal[a] BY <1>x
      <3>2. ~ \E vv \in Values : VotedForIn(a, vv, c) BY <2>1, <3>1
      <3>3. VotedForIn(a, v, c) BY <1>x, <1>nm, VotedForIn_Add_Non2b
      <3> QED BY <3>2, <3>3
    <2> QED BY <2>2, <2>3, <2>4, <2>5
  <1> QED BY <1>1, <1>2, <1>3

LEMMA Phase2bInv ==
  ASSUME Inv, NEW a0 \in Acceptors, Phase2b(a0)
  PROVE  Inv'
PROOF
  <1> USE DEF Inv
  <1>tk. /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
         /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
         /\ maxVal \in [Acceptors -> Values \cup {None}]
         /\ msgs \in SUBSET Messages
    BY DEF TypeOK
  <1>0. PICK m0 \in msgs :
            /\ m0.type = "2a"
            /\ m0.bal >= maxBal[a0]
            /\ maxVBal' = [maxVBal EXCEPT ![a0] = m0.bal]
            /\ maxBal' = [maxBal EXCEPT ![a0] = m0.bal]
            /\ maxVal' = [maxVal EXCEPT ![a0] = m0.val]
            /\ Send([type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0])
    BY DEF Phase2b
  <1>m. m0 \in Messages /\ m0.bal \in Ballots /\ m0.val \in Values
    BY <1>0, <1>tk DEF Messages
  <1>x. /\ msgs' = msgs \cup {[type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0]}
        /\ maxBal' = [maxBal EXCEPT ![a0] = m0.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a0] = m0.bal]
        /\ maxVal' = [maxVal EXCEPT ![a0] = m0.val]
    BY <1>0 DEF Send
  <1>nm. /\ [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0].type = "2b"
         /\ [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0].bal = m0.bal
         /\ [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0].val = m0.val
         /\ [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0].acc = a0
    OBVIOUS
  <1>sub. msgs \subseteq msgs' BY <1>x
  <1>old. maxBal[a0] \in Ballots \cup {-1}
          /\ maxVBal[a0] \in Ballots \cup {-1}
          /\ maxVal[a0] \in Values \cup {None}
          /\ maxBal[a0] >= maxVBal[a0]
    BY <1>tk DEF TypeOK
  <1>mb. /\ maxBal[a0] =< m0.bal
         /\ maxVBal[a0] =< maxBal[a0]
         /\ maxVBal[a0] =< m0.bal
    <2>1. maxBal[a0] \in Ballots \cup {-1} /\ maxVBal[a0] \in Ballots \cup {-1} BY <1>old
    <2>2. m0.bal >= maxBal[a0] BY <1>0
    <2>3. maxBal[a0] >= maxVBal[a0] BY <1>old
    <2> QED BY <2>1, <2>2, <2>3, <1>m DEF Ballots
  <1>maxBal_a. \A a \in Acceptors : maxBal[a]' = IF a = a0 THEN m0.bal ELSE maxBal[a]
    BY <1>x, <1>tk
  <1>maxVBal_a. \A a \in Acceptors : maxVBal[a]' = IF a = a0 THEN m0.bal ELSE maxVBal[a]
    BY <1>x, <1>tk
  <1>maxVal_a. \A a \in Acceptors : maxVal[a]' = IF a = a0 THEN m0.val ELSE maxVal[a]
    BY <1>x, <1>tk
  <1>1. TypeOK'
    <2>1. [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0] \in Messages
      BY <1>m DEF Messages
    <2>2. msgs' \subseteq Messages BY <1>x, <2>1, <1>tk
    <2>3. maxBal' \in [Acceptors -> Ballots \cup {-1}] BY <1>x, <1>m, <1>tk
    <2>4. maxVBal' \in [Acceptors -> Ballots \cup {-1}] BY <1>x, <1>m, <1>tk
    <2>5. maxVal' \in [Acceptors -> Values \cup {None}] BY <1>x, <1>m, <1>tk
    <2>6. \A a \in Acceptors : maxBal[a]' >= maxVBal[a]'
      <3> SUFFICES ASSUME NEW a \in Acceptors PROVE maxBal[a]' >= maxVBal[a]'
          OBVIOUS
      <3>1. CASE a = a0
        <4>1. maxBal[a]' = m0.bal /\ maxVBal[a]' = m0.bal BY <1>maxBal_a, <1>maxVBal_a, <3>1
        <4> QED BY <4>1, <1>m DEF Ballots
      <3>2. CASE a # a0
        <4>1. maxBal[a]' = maxBal[a] /\ maxVBal[a]' = maxVBal[a]
             BY <1>maxBal_a, <1>maxVBal_a, <3>2
        <4>2. maxBal[a] >= maxVBal[a] BY DEF TypeOK
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  <1>vf_a0. VotedForIn(a0, m0.val, m0.bal)'
    <2> DEFINE newm == [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0]
    <2>1. newm \in msgs' BY <1>x
    <2>2. newm.type = "2b" /\ newm.val = m0.val /\ newm.bal = m0.bal /\ newm.acc = a0
      OBVIOUS
    <2> QED BY <2>1, <2>2 DEF VotedForIn
  <1>vf_split. ASSUME NEW aa, NEW vv, NEW cc, VotedForIn(aa, vv, cc)'
               PROVE VotedForIn(aa, vv, cc) \/ (aa = a0 /\ vv = m0.val /\ cc = m0.bal)
    <2>0. \E m \in msgs' : m.type = "2b" /\ m.val = vv /\ m.bal = cc /\ m.acc = aa
        BY <1>vf_split DEF VotedForIn
    <2>1. PICK m \in msgs' : m.type = "2b" /\ m.val = vv /\ m.bal = cc /\ m.acc = aa
        BY <2>0
    <2>2. m \in msgs \cup {[type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0]}
        BY <1>x, <2>1
    <2>3. CASE m \in msgs
       BY <2>3, <2>1 DEF VotedForIn
    <2>4. CASE m = [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0]
       BY <2>4, <2>1
    <2> QED BY <2>2, <2>3, <2>4
  <1>2. MsgInv'
    <2> DEFINE newm2b == [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> a0]
    <2> SUFFICES ASSUME NEW m \in msgs'
                 PROVE  /\ (m.type = "1b") =>
                            /\ m.bal =< maxBal[m.acc]'
                            /\ \/ /\ m.maxVal \in Values
                                  /\ m.maxVBal \in Ballots
                                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                               \/ /\ m.maxVal = None
                                  /\ m.maxVBal = -1
                            /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                  ~ \E v \in Values : VotedForIn(m.acc, v, c)'
                        /\ (m.type = "2a") =>
                              /\ SafeAt(m.val, m.bal)'
                              /\ \A ma \in msgs' :
                                   (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                        /\ (m.type = "2b") =>
                              /\ \E ma \in msgs' : /\ ma.type = "2a"
                                                   /\ ma.bal  = m.bal
                                                   /\ ma.val  = m.val
                              /\ m.bal =< maxVBal[m.acc]'
        BY DEF MsgInv
    <2>1. CASE m = newm2b
      <3>1. m.type = "2b" /\ m.bal = m0.bal /\ m.val = m0.val /\ m.acc = a0 BY <2>1
      <3>2. \E ma \in msgs' : ma.type = "2a" /\ ma.bal = m.bal /\ ma.val = m.val
        <4>1. m0 \in msgs' BY <1>x
        <4> QED BY <4>1, <1>0, <3>1
      <3>3. m.bal =< maxVBal[m.acc]'
        <4>1. maxVBal[a0]' = m0.bal BY <1>maxVBal_a
        <4> QED BY <4>1, <3>1, <1>m DEF Ballots
      <3> QED BY <3>1, <3>2, <3>3
    <2>2. CASE m \in msgs
      <3>m_type. m \in Messages BY <2>2, <1>tk
      <3>1. ASSUME m.type = "1b"
            PROVE  /\ m.bal =< maxBal[m.acc]'
                   /\ \/ /\ m.maxVal \in Values
                         /\ m.maxVBal \in Ballots
                         /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                      \/ /\ m.maxVal = None
                         /\ m.maxVBal = -1
                   /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                         ~ \E v \in Values : VotedForIn(m.acc, v, c)'
        <4>m_field. m.acc \in Acceptors /\ m.bal \in Ballots
                    /\ m.maxVBal \in Ballots \cup {-1}
                    /\ m.maxVal \in Values \cup {None}
          BY <3>m_type, <3>1 DEF Messages
        <4>1. /\ m.bal =< maxBal[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E v \in Values : VotedForIn(m.acc, v, c)
          BY <2>2, <3>1 DEF MsgInv
        <4>2. m.bal =< maxBal[m.acc]'
          <5>1. CASE m.acc = a0
            <6>1. maxBal[m.acc]' = m0.bal BY <1>maxBal_a, <4>m_field, <5>1
            <6>2. m.bal =< maxBal[m.acc] BY <4>1
            <6>3. m.bal =< maxBal[a0] BY <6>2, <5>1
            <6>4. maxBal[a0] =< m0.bal BY <1>mb
            <6>5. maxBal[m.acc] \in Ballots \cup {-1} BY <4>m_field, <1>tk
            <6> QED BY <6>1, <6>3, <6>4, <6>5, <4>m_field, <1>m, <5>1 DEF Ballots
          <5>2. CASE m.acc # a0
            <6>1. maxBal[m.acc]' = maxBal[m.acc] BY <1>maxBal_a, <4>m_field, <5>2
            <6> QED BY <6>1, <4>1
          <5> QED BY <5>1, <5>2
        <4>3. \/ /\ m.maxVal \in Values
                 /\ m.maxVBal \in Ballots
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              \/ /\ m.maxVal = None
                 /\ m.maxVBal = -1
          <5>1. CASE /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            <6>1. PICK mm \in msgs : mm.type = "2b" /\ mm.val = m.maxVal /\ mm.bal = m.maxVBal /\ mm.acc = m.acc
                BY <5>1 DEF VotedForIn
            <6>2. mm \in msgs' BY <6>1, <1>sub
            <6> QED BY <5>1, <6>1, <6>2 DEF VotedForIn
          <5>2. CASE m.maxVal = None /\ m.maxVBal = -1 BY <5>2
          <5> QED BY <4>1, <5>1, <5>2
        <4>4. \A c \in (m.maxVBal+1) .. (m.bal-1) :
                ~ \E v \in Values : VotedForIn(m.acc, v, c)'
          <5> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1),
                              NEW v \in Values, VotedForIn(m.acc, v, c)'
                       PROVE FALSE OBVIOUS
          <5>1. ~ \E vv \in Values : VotedForIn(m.acc, vv, c) BY <4>1
          <5>2. VotedForIn(m.acc, v, c) \/ (m.acc = a0 /\ v = m0.val /\ c = m0.bal)
            BY <1>vf_split
          <5>3. m.acc = a0 /\ v = m0.val /\ c = m0.bal BY <5>1, <5>2
          <5>4. m.bal =< maxBal[m.acc] BY <4>1
          <5>5. m.bal =< maxBal[a0] BY <5>3, <5>4
          <5>6. maxBal[a0] =< m0.bal BY <1>mb
          <5>7. m.bal =< m0.bal BY <5>5, <5>6, <1>old, <1>m, <4>m_field DEF Ballots
          <5>8. c =< m.bal - 1
            <6>1. m.maxVBal + 1 \in Int BY <4>m_field DEF Ballots
            <6>2. m.bal - 1 \in Int BY <4>m_field DEF Ballots
            <6> QED BY <6>1, <6>2
          <5>9. m0.bal =< m.bal - 1 BY <5>3, <5>8
          <5>10. m0.bal < m.bal BY <5>9, <1>m, <4>m_field DEF Ballots
          <5> QED BY <5>7, <5>10, <1>m, <4>m_field DEF Ballots
        <4> QED BY <4>2, <4>3, <4>4
      <3>2. ASSUME m.type = "2a"
            PROVE  /\ SafeAt(m.val, m.bal)'
                   /\ \A ma \in msgs' :
                         (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        <4>m_field. m.val \in Values /\ m.bal \in Ballots
          BY <3>m_type, <3>2 DEF Messages
        <4>1. SafeAt(m.val, m.bal) BY <2>2, <3>2 DEF MsgInv
        <4>2. SafeAt(m.val, m.bal)'
          <5> SUFFICES ASSUME NEW d \in 0..(m.bal-1)
                       PROVE  \E Q \in Quorums :
                                \A aa \in Q : VotedForIn(aa, m.val, d)' \/ WontVoteIn(aa, d)'
              BY DEF SafeAt
          <5>d. d \in Nat /\ d >= 0 /\ d <= m.bal - 1 /\ d < m.bal /\ d \in Int
            BY <4>m_field DEF Ballots
          <5>1. \E Q \in Quorums : \A aa \in Q : VotedForIn(aa, m.val, d) \/ WontVoteIn(aa, d)
            BY <4>1 DEF SafeAt
          <5>2. PICK Q \in Quorums : \A aa \in Q : VotedForIn(aa, m.val, d) \/ WontVoteIn(aa, d)
            BY <5>1
          <5>3. \A aa \in Q : VotedForIn(aa, m.val, d)' \/ WontVoteIn(aa, d)'
            <6> SUFFICES ASSUME NEW aa \in Q
                         PROVE  VotedForIn(aa, m.val, d)' \/ WontVoteIn(aa, d)'
                OBVIOUS
            <6>0. aa \in Acceptors BY QuorumAssumption
            <6>1. VotedForIn(aa, m.val, d) \/ WontVoteIn(aa, d) BY <5>2
            <6>2. CASE VotedForIn(aa, m.val, d) BY <6>2, <1>sub, VotedForIn_Mono
            <6>3. CASE WontVoteIn(aa, d)
              <7>1. \A v \in Values : ~VotedForIn(aa, v, d) BY <6>3 DEF WontVoteIn
              <7>2. maxBal[aa] > d BY <6>3 DEF WontVoteIn
              <7>3. \A v \in Values : ~VotedForIn(aa, v, d)'
                <8> SUFFICES ASSUME NEW v \in Values, VotedForIn(aa, v, d)' PROVE FALSE OBVIOUS
                <8>1. VotedForIn(aa, v, d) \/ (aa = a0 /\ v = m0.val /\ d = m0.bal)
                    BY <1>vf_split
                <8>2. ~VotedForIn(aa, v, d) BY <7>1
                <8>3. aa = a0 /\ v = m0.val /\ d = m0.bal BY <8>1, <8>2
                <8>4. maxBal[a0] > d BY <7>2, <8>3
                <8>5. d = m0.bal BY <8>3
                <8>6. maxBal[a0] > m0.bal BY <8>4, <8>5
                <8>7. maxBal[a0] \in Ballots \cup {-1} BY <1>old
                <8>8. maxBal[a0] =< m0.bal BY <1>mb
                <8> QED BY <8>6, <8>8, <8>7, <1>m DEF Ballots
              <7>4. maxBal[aa]' > d
                <8>1. CASE aa = a0
                  <9>1. maxBal[aa]' = m0.bal BY <1>maxBal_a, <6>0, <8>1
                  <9>2. m0.bal >= maxBal[a0] BY <1>mb
                  <9>3. maxBal[a0] > d BY <7>2, <8>1
                  <9>4. maxBal[a0] \in Ballots \cup {-1} BY <1>old
                  <9>5. m0.bal > d BY <9>2, <9>3, <9>4, <1>m, <5>d DEF Ballots
                  <9> QED BY <9>1, <9>5
                <8>2. CASE aa # a0
                  <9>1. maxBal[aa]' = maxBal[aa] BY <1>maxBal_a, <6>0, <8>2
                  <9> QED BY <9>1, <7>2
                <8> QED BY <8>1, <8>2
              <7>5. WontVoteIn(aa, d)' BY <7>3, <7>4 DEF WontVoteIn
              <7> QED BY <7>5
            <6> QED BY <6>1, <6>2, <6>3
          <5> QED BY <5>3
        <4>3. \A ma \in msgs' :
                 (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
          <5> SUFFICES ASSUME NEW ma \in msgs',
                              ma.type = "2a", ma.bal = m.bal
                       PROVE  ma = m
              OBVIOUS
          <5>1. ma \in msgs \cup {newm2b} BY <1>x
          <5>2. ma # newm2b OBVIOUS
          <5>3. ma \in msgs BY <5>1, <5>2
          <5>4. \A ma2 \in msgs :
                  (ma2.type = "2a") /\ (ma2.bal = m.bal) => (ma2 = m)
            BY <2>2, <3>2 DEF MsgInv
          <5> QED BY <5>3, <5>4
        <4> QED BY <4>2, <4>3
      <3>3. ASSUME m.type = "2b"
            PROVE  /\ \E ma \in msgs' : /\ ma.type = "2a"
                                       /\ ma.bal  = m.bal
                                       /\ ma.val  = m.val
                   /\ m.bal =< maxVBal[m.acc]'
        <4>m_field. m.acc \in Acceptors /\ m.bal \in Ballots
          BY <3>m_type, <3>3 DEF Messages
        <4>1. /\ \E ma \in msgs : /\ ma.type = "2a"
                                 /\ ma.bal  = m.bal
                                 /\ ma.val  = m.val
              /\ m.bal =< maxVBal[m.acc]
          BY <2>2, <3>3 DEF MsgInv
        <4>2. PICK ma \in msgs : ma.type = "2a" /\ ma.bal = m.bal /\ ma.val = m.val
          BY <4>1
        <4>3. ma \in msgs' BY <1>x, <4>2
        <4>4. m.bal =< maxVBal[m.acc]'
          <5>1. m.bal =< maxVBal[m.acc] BY <4>1
          <5>2. CASE m.acc = a0
            <6>1. maxVBal[m.acc]' = m0.bal BY <1>maxVBal_a, <4>m_field, <5>2
            <6>2. maxVBal[a0] =< m0.bal BY <1>mb
            <6>3. m.bal =< maxVBal[a0] BY <5>1, <5>2
            <6>4. m.bal =< m0.bal BY <6>3, <6>2, <1>old, <1>m, <4>m_field DEF Ballots
            <6> QED BY <6>1, <6>4, <1>m, <4>m_field DEF Ballots
          <5>3. CASE m.acc # a0
            <6>1. maxVBal[m.acc]' = maxVBal[m.acc] BY <1>maxVBal_a, <4>m_field, <5>3
            <6> QED BY <6>1, <5>1
          <5> QED BY <5>2, <5>3
        <4> QED BY <4>2, <4>3, <4>4
      <3> QED BY <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2, <1>x
  <1>3. AccInv'
    <2> SUFFICES ASSUME NEW a \in Acceptors
                 PROVE  /\ (maxVal[a]' = None) <=> (maxVBal[a]' = -1)
                        /\ maxVBal[a]' =< maxBal[a]'
                        /\ (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
                        /\ \A c \in Ballots : c > maxVBal[a]' =>
                                ~ \E v \in Values : VotedForIn(a, v, c)'
        BY DEF AccInv
    <2>1. /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
          /\ maxVBal[a] =< maxBal[a]
          /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
          /\ \A c \in Ballots : c > maxVBal[a] =>
                  ~ \E v \in Values : VotedForIn(a, v, c)
       BY DEF AccInv
    <2>2. CASE a = a0
      <3>vala. maxVal[a]' = m0.val BY <1>maxVal_a, <2>2
      <3>vba. maxVBal[a]' = m0.bal BY <1>maxVBal_a, <2>2
      <3>ba. maxBal[a]' = m0.bal BY <1>maxBal_a, <2>2
      <3>1. (maxVal[a]' = None) <=> (maxVBal[a]' = -1)
        <4>1. m0.val # None BY <1>m, NoneNotAValue
        <4>2. m0.bal # -1 BY <1>m DEF Ballots
        <4> QED BY <3>vala, <3>vba, <4>1, <4>2
      <3>2. maxVBal[a]' =< maxBal[a]' BY <3>vba, <3>ba, <1>m DEF Ballots
      <3>3. (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
        <4>1. ASSUME maxVBal[a]' >= 0 PROVE VotedForIn(a, maxVal[a], maxVBal[a])'
          <5>1. VotedForIn(a0, m0.val, m0.bal)' BY <1>vf_a0
          <5>2. a = a0 BY <2>2
          <5>3. VotedForIn(a, m0.val, m0.bal)' BY <5>1, <5>2
          <5>4. maxVal[a]' = m0.val /\ maxVBal[a]' = m0.bal BY <3>vala, <3>vba
          <5> QED BY <5>3, <5>4 DEF VotedForIn
        <4> QED BY <4>1
      <3>4. \A c \in Ballots : c > maxVBal[a]' =>
                ~ \E v \in Values : VotedForIn(a, v, c)'
        <4> SUFFICES ASSUME NEW c \in Ballots, c > maxVBal[a]',
                            NEW v \in Values, VotedForIn(a, v, c)'
                     PROVE  FALSE
            OBVIOUS
        <4>1. c > m0.bal BY <3>vba
        <4>2. c # m0.bal BY <4>1, <1>m DEF Ballots
        <4>3. VotedForIn(a, v, c) \/ (a = a0 /\ v = m0.val /\ c = m0.bal)
            BY <1>vf_split
        <4>4. VotedForIn(a, v, c) BY <4>2, <4>3
        <4>5. c > maxVBal[a]
          <5>1. maxVBal[a] =< maxBal[a] BY <2>1
          <5>2. maxBal[a] =< m0.bal BY <1>mb, <2>2
          <5>3. maxVBal[a] \in Ballots \cup {-1} BY <1>old, <2>2
          <5>4. maxBal[a] \in Ballots \cup {-1} BY <1>old, <2>2
          <5>5. maxVBal[a] =< m0.bal BY <5>1, <5>2, <5>3, <5>4, <1>m DEF Ballots
          <5> QED BY <5>5, <4>1, <5>3, <1>m DEF Ballots
        <4>6. ~ \E vv \in Values : VotedForIn(a, vv, c) BY <2>1, <4>5
        <4> QED BY <4>4, <4>6
      <3> QED BY <3>1, <3>2, <3>3, <3>4
    <2>3. CASE a # a0
      <3>vala. maxVal[a]' = maxVal[a] BY <1>maxVal_a, <2>3
      <3>vba. maxVBal[a]' = maxVBal[a] BY <1>maxVBal_a, <2>3
      <3>ba. maxBal[a]' = maxBal[a] BY <1>maxBal_a, <2>3
      <3>1. (maxVal[a]' = None) <=> (maxVBal[a]' = -1) BY <3>vala, <3>vba, <2>1
      <3>2. maxVBal[a]' =< maxBal[a]' BY <3>vba, <3>ba, <2>1
      <3>3. (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
        <4>1. ASSUME maxVBal[a]' >= 0 PROVE VotedForIn(a, maxVal[a], maxVBal[a])'
          <5>1. maxVBal[a] >= 0 BY <4>1, <3>vba
          <5>2. VotedForIn(a, maxVal[a], maxVBal[a]) BY <5>1, <2>1
          <5>3. PICK mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a] /\ mm.bal = maxVBal[a] /\ mm.acc = a
                BY <5>2 DEF VotedForIn
          <5>4. mm \in msgs' BY <5>3, <1>sub
          <5>5. maxVal[a]' = maxVal[a] /\ maxVBal[a]' = maxVBal[a] BY <3>vala, <3>vba
          <5> QED BY <5>3, <5>4, <5>5 DEF VotedForIn
        <4> QED BY <4>1
      <3>4. \A c \in Ballots : c > maxVBal[a]' =>
                ~ \E v \in Values : VotedForIn(a, v, c)'
        <4> SUFFICES ASSUME NEW c \in Ballots, c > maxVBal[a]',
                            NEW v \in Values, VotedForIn(a, v, c)'
                     PROVE  FALSE
            OBVIOUS
        <4>1. c > maxVBal[a] BY <3>vba
        <4>2. ~ \E vv \in Values : VotedForIn(a, vv, c) BY <2>1, <4>1
        <4>3. ~ VotedForIn(a, v, c) BY <4>2
        <4>4. VotedForIn(a, v, c) \/ (a = a0 /\ v = m0.val /\ c = m0.bal)
            BY <1>vf_split
        <4> QED BY <4>3, <4>4, <2>3
      <3> QED BY <3>1, <3>2, <3>3, <3>4
    <2> QED BY <2>2, <2>3
  <1> QED BY <1>1, <1>2, <1>3

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
PROOF
  <1> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
       OBVIOUS
  <1>1. CASE UNCHANGED vars
    <2>1. /\ msgs' = msgs
          /\ maxBal' = maxBal
          /\ maxVBal' = maxVBal
          /\ maxVal' = maxVal
      BY <1>1 DEF vars
    <2>vf. ASSUME NEW aa, NEW vv, NEW cc
           PROVE VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
      <3>1. msgs' = msgs BY <2>1
      <3> QED BY <3>1 DEF VotedForIn
    <2>2. TypeOK' BY <2>1 DEF Inv, TypeOK
    <2>3. MsgInv'
      <3> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  /\ (m.type = "1b") =>
                              /\ m.bal =< maxBal[m.acc]'
                              /\ \/ /\ m.maxVal \in Values
                                    /\ m.maxVBal \in Ballots
                                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                                 \/ /\ m.maxVal = None
                                    /\ m.maxVBal = -1
                              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                    ~ \E v \in Values : VotedForIn(m.acc, v, c)'
                          /\ (m.type = "2a") =>
                                /\ SafeAt(m.val, m.bal)'
                                /\ \A ma \in msgs' :
                                     (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                          /\ (m.type = "2b") =>
                                /\ \E ma \in msgs' : /\ ma.type = "2a"
                                                     /\ ma.bal  = m.bal
                                                     /\ ma.val  = m.val
                                /\ m.bal =< maxVBal[m.acc]'
          BY DEF MsgInv
      <3>m. m \in msgs BY <2>1
      <3>old. /\ (m.type = "1b") =>
                  /\ m.bal =< maxBal[m.acc]
                  /\ \/ /\ m.maxVal \in Values
                        /\ m.maxVBal \in Ballots
                        /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                     \/ /\ m.maxVal = None
                        /\ m.maxVBal = -1
                  /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                        ~ \E v \in Values : VotedForIn(m.acc, v, c)
              /\ (m.type = "2a") =>
                    /\ SafeAt(m.val, m.bal)
                    /\ \A ma \in msgs :
                         (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
              /\ (m.type = "2b") =>
                    /\ \E ma \in msgs : /\ ma.type = "2a"
                                        /\ ma.bal  = m.bal
                                        /\ ma.val  = m.val
                    /\ m.bal =< maxVBal[m.acc]
        BY <3>m DEF Inv, MsgInv
      <3>1. ASSUME m.type = "1b"
            PROVE  /\ m.bal =< maxBal[m.acc]'
                   /\ \/ /\ m.maxVal \in Values
                         /\ m.maxVBal \in Ballots
                         /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                      \/ /\ m.maxVal = None
                         /\ m.maxVBal = -1
                   /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                         ~ \E v \in Values : VotedForIn(m.acc, v, c)'
        <4>1. /\ m.bal =< maxBal[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E v \in Values : VotedForIn(m.acc, v, c)
          BY <3>old, <3>1
        <4>2. m.bal =< maxBal[m.acc]' BY <4>1, <2>1
        <4>3. \/ /\ m.maxVal \in Values
                 /\ m.maxVBal \in Ballots
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              \/ /\ m.maxVal = None
                 /\ m.maxVBal = -1
          <5>1. CASE /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            BY <5>1, <2>vf
          <5>2. CASE m.maxVal = None /\ m.maxVBal = -1 BY <5>2
          <5> QED BY <4>1, <5>1, <5>2
        <4>4. \A c \in (m.maxVBal+1) .. (m.bal-1) :
                ~ \E v \in Values : VotedForIn(m.acc, v, c)'
          <5> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1),
                              NEW v \in Values, VotedForIn(m.acc, v, c)'
                       PROVE FALSE OBVIOUS
          <5>1. ~ \E vv \in Values : VotedForIn(m.acc, vv, c) BY <4>1
          <5>2. VotedForIn(m.acc, v, c) BY <2>vf
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>2, <4>3, <4>4
      <3>2. ASSUME m.type = "2a"
            PROVE  /\ SafeAt(m.val, m.bal)'
                   /\ \A ma \in msgs' :
                         (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        <4>1. /\ SafeAt(m.val, m.bal)
              /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
          BY <3>old, <3>2
        <4>2. SafeAt(m.val, m.bal)'
          <5> SUFFICES ASSUME NEW c \in 0..(m.bal-1)
                       PROVE  \E Q \in Quorums :
                                \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
              BY DEF SafeAt
          <5>1. \E Q \in Quorums :
                  \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
            BY <4>1 DEF SafeAt
          <5>2. PICK Q \in Quorums :
                  \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
            BY <5>1
          <5>3. \A aa \in Q : VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
            <6> SUFFICES ASSUME NEW aa \in Q
                         PROVE  VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
                OBVIOUS
            <6>1. VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c) BY <5>2
            <6>2. CASE VotedForIn(aa, m.val, c) BY <6>2, <2>vf
            <6>3. CASE WontVoteIn(aa, c)
              <7>1. \A vv \in Values : ~VotedForIn(aa, vv, c) BY <6>3 DEF WontVoteIn
              <7>2. \A vv \in Values : ~VotedForIn(aa, vv, c)'
                <8> SUFFICES ASSUME NEW vv \in Values, VotedForIn(aa, vv, c)'
                             PROVE FALSE OBVIOUS
                <8>1. VotedForIn(aa, vv, c) BY <2>vf
                <8> QED BY <8>1, <7>1
              <7>3. maxBal[aa] > c BY <6>3 DEF WontVoteIn
              <7>4. maxBal[aa]' > c BY <2>1, <7>3
              <7> QED BY <7>2, <7>4 DEF WontVoteIn
            <6> QED BY <6>1, <6>2, <6>3
          <5> QED BY <5>3
        <4>3. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
          BY <4>1, <2>1
        <4> QED BY <4>2, <4>3
      <3>3. ASSUME m.type = "2b"
            PROVE  /\ \E ma \in msgs' : /\ ma.type = "2a"
                                       /\ ma.bal  = m.bal
                                       /\ ma.val  = m.val
                   /\ m.bal =< maxVBal[m.acc]'
        <4>1. /\ \E ma \in msgs : /\ ma.type = "2a"
                                 /\ ma.bal  = m.bal
                                 /\ ma.val  = m.val
              /\ m.bal =< maxVBal[m.acc]
          BY <3>old, <3>3
        <4> QED BY <4>1, <2>1
      <3> QED BY <3>1, <3>2, <3>3
    <2>4. AccInv'
      <3> SUFFICES ASSUME NEW a \in Acceptors
                   PROVE  /\ (maxVal[a]' = None) <=> (maxVBal[a]' = -1)
                          /\ maxVBal[a]' =< maxBal[a]'
                          /\ (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
                          /\ \A c \in Ballots : c > maxVBal[a]' =>
                                  ~ \E v \in Values : VotedForIn(a, v, c)'
          BY DEF AccInv
      <3>1. /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
            /\ maxVBal[a] =< maxBal[a]
            /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
            /\ \A c \in Ballots : c > maxVBal[a] =>
                    ~ \E v \in Values : VotedForIn(a, v, c)
         BY DEF Inv, AccInv
      <3>2. (maxVal[a]' = None) <=> (maxVBal[a]' = -1) BY <3>1, <2>1
      <3>3. maxVBal[a]' =< maxBal[a]' BY <3>1, <2>1
      <3>4. (maxVBal[a]' >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
        <4>1. ASSUME maxVBal[a]' >= 0 PROVE VotedForIn(a, maxVal[a], maxVBal[a])'
          <5>1. maxVBal[a] >= 0 BY <4>1, <2>1
          <5>2. VotedForIn(a, maxVal[a], maxVBal[a]) BY <5>1, <3>1
          <5>3. PICK mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a] /\ mm.bal = maxVBal[a] /\ mm.acc = a
                BY <5>2 DEF VotedForIn
          <5>4. mm \in msgs' BY <5>3, <2>1
          <5>5. maxVal[a]' = maxVal[a] /\ maxVBal[a]' = maxVBal[a] BY <2>1
          <5> QED BY <5>3, <5>4, <5>5 DEF VotedForIn
        <4> QED BY <4>1
      <3>5. \A c \in Ballots : c > maxVBal[a]' =>
                ~ \E v \in Values : VotedForIn(a, v, c)'
        <4> SUFFICES ASSUME NEW c \in Ballots, c > maxVBal[a]',
                            NEW v \in Values, VotedForIn(a, v, c)'
                     PROVE  FALSE
            OBVIOUS
        <4>1. c > maxVBal[a] BY <2>1
        <4>2. ~ \E vv \in Values : VotedForIn(a, vv, c) BY <3>1, <4>1
        <4>3. VotedForIn(a, v, c) BY <2>vf
        <4> QED BY <4>2, <4>3
      <3> QED BY <3>2, <3>3, <3>4, <3>5
    <2> QED BY <2>2, <2>3, <2>4 DEF Inv
  <1>2. CASE Next
    <2>1. CASE \E b \in Ballots : Phase1a(b)
      <3>1. PICK b \in Ballots : Phase1a(b) BY <2>1
      <3> QED BY Phase1aInv, <3>1
    <2>2. CASE \E a \in Acceptors : Phase1b(a)
      <3>1. PICK a \in Acceptors : Phase1b(a) BY <2>2
      <3> QED BY Phase1bInv, <3>1
    <2>3. CASE \E b \in Ballots : Phase2a(b)
      <3>1. PICK b \in Ballots : Phase2a(b) BY <2>3
      <3> QED BY Phase2aInv, <3>1
    <2>4. CASE \E a \in Acceptors : Phase2b(a)
      <3>1. PICK a \in Acceptors : Phase2b(a) BY <2>4
      <3> QED BY Phase2bInv, <3>1
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <1>2 DEF Next
  <1> QED BY <1>1, <1>2

THEOREM Invariant == Spec => []Inv
PROOF
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv' BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------

=============================================================================
