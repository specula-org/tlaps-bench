------------------------------- MODULE Paxos_Consistent -------------------------------

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

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
-----------------------------------------------------------------------------
(* Auxiliary definitions for the inductive proof *)

Messages ==
  [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, bal : Ballots,
        maxVBal : Ballots \cup {-1},
        maxVal : Values \cup {None},
        acc : Acceptors]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK ==
  /\ msgs \in SUBSET Messages
  /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVal \in [Acceptors -> Values \cup {None}]

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
        /\ \/ m.maxVBal = -1
           \/ /\ m.maxVBal \in 0..(m.bal - 1)
              /\ m.maxVal \in Values
              /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
        /\ \A b \in (m.maxVBal + 1)..(m.bal - 1) :
             \A v \in Values : ~ VotedForIn(m.acc, v, b)
    /\ (m.type = "2a") =>
        /\ SafeAt(m.val, m.bal)
        /\ \A m2 \in msgs :
             (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
    /\ (m.type = "2b") =>
         \E m2 \in msgs : /\ m2.type = "2a"
                          /\ m2.bal = m.bal
                          /\ m2.val = m.val

AccInv ==
  \A a \in Acceptors :
    /\ maxBal[a] >= maxVBal[a]
    /\ (maxVBal[a] # -1) =>
          /\ maxVBal[a] \in Nat
          /\ maxVal[a] \in Values
          /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                 /\ mm.bal = maxVBal[a] /\ mm.acc = a
    /\ \A v \in Values, b \in Ballots :
          VotedForIn(a, v, b) => maxVBal[a] >= b

IndInv == TypeOK /\ MsgInv /\ AccInv

-----------------------------------------------------------------------------
(* Lemmas *)

LEMMA Voted_Implies_2a ==
  ASSUME MsgInv, NEW a, NEW v, NEW b, VotedForIn(a, v, b)
  PROVE \E mm \in msgs : mm.type = "2a" /\ mm.bal = b /\ mm.val = v
PROOF
  <1>1. PICK m2b \in msgs :
          m2b.type = "2b" /\ m2b.val = v /\ m2b.bal = b /\ m2b.acc = a
    BY DEF VotedForIn
  <1>2. QED BY <1>1 DEF MsgInv

LEMMA TwoA_Unique ==
  ASSUME MsgInv, NEW m1 \in msgs, NEW m2 \in msgs,
         m1.type = "2a", m2.type = "2a", m1.bal = m2.bal
  PROVE m1.val = m2.val
PROOF
  BY DEF MsgInv

LEMMA Votes_Unique ==
  ASSUME MsgInv, NEW a, NEW b, NEW v1, NEW v2,
         VotedForIn(a, v1, b), VotedForIn(a, v2, b)
  PROVE v1 = v2
PROOF
  <1>1. PICK m1 \in msgs : m1.type = "2a" /\ m1.bal = b /\ m1.val = v1
    BY Voted_Implies_2a
  <1>2. PICK m2 \in msgs : m2.type = "2a" /\ m2.bal = b /\ m2.val = v2
    BY Voted_Implies_2a
  <1>3. QED BY <1>1, <1>2, TwoA_Unique

LEMMA Cons_Lemma == IndInv => Consistency
PROOF
  <1> SUFFICES ASSUME IndInv,
                      NEW v1 \in Values, NEW v2 \in Values,
                      Chosen(v1), Chosen(v2)
               PROVE v1 = v2
    BY DEF Consistency
  <1>0. MsgInv BY DEF IndInv
  <1>1a. PICK b1 \in Ballots : ChosenIn(v1, b1)
    BY DEF Chosen
  <1>1b. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
    BY <1>1a DEF ChosenIn
  <1>2a. PICK b2 \in Ballots : ChosenIn(v2, b2)
    BY DEF Chosen
  <1>2b. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
    BY <1>2a DEF ChosenIn
  <1>3. b1 \in Nat /\ b2 \in Nat
    BY DEF Ballots
  <1>4. Q1 \subseteq Acceptors /\ Q2 \subseteq Acceptors
    BY QuorumAssumption
  <1>5. CASE b1 = b2
    <2>1. PICK a \in Q1 \cap Q2 : TRUE
      BY QuorumAssumption
    <2>2. VotedForIn(a, v1, b1) /\ VotedForIn(a, v2, b1)
      BY <1>1b, <1>2b, <2>1, <1>5
    <2>3. QED BY <2>2, Votes_Unique, <1>0
  <1>6. CASE b1 < b2
    <2>1. PICK ao \in Q2 : TRUE
      BY QuorumAssumption
    <2>2. VotedForIn(ao, v2, b2)
      BY <1>2b, <2>1
    <2>3. PICK m2a \in msgs : m2a.type = "2a" /\ m2a.bal = b2 /\ m2a.val = v2
      BY Voted_Implies_2a, <2>2, <1>0
    <2>4. SafeAt(v2, b2)
      BY <2>3, <1>0 DEF MsgInv
    <2>5. b1 \in 0..(b2-1)
      BY <1>3, <1>6
    <2>6. PICK Q3 \in Quorums :
            \A a \in Q3 : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
      BY <2>4, <2>5 DEF SafeAt
    <2>7. PICK a \in Q1 \cap Q3 : TRUE
      BY QuorumAssumption
    <2>8. VotedForIn(a, v1, b1)
      BY <1>1b, <2>7
    <2>9. VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
      BY <2>6, <2>7
    <2>10. ~ WontVoteIn(a, b1)
      BY <2>8 DEF WontVoteIn
    <2>11. VotedForIn(a, v2, b1)
      BY <2>9, <2>10
    <2>12. QED BY <2>8, <2>11, Votes_Unique, <1>0
  <1>7. CASE b2 < b1
    <2>1. PICK ao \in Q1 : TRUE
      BY QuorumAssumption
    <2>2. VotedForIn(ao, v1, b1)
      BY <1>1b, <2>1
    <2>3. PICK m2a \in msgs : m2a.type = "2a" /\ m2a.bal = b1 /\ m2a.val = v1
      BY Voted_Implies_2a, <2>2, <1>0
    <2>4. SafeAt(v1, b1)
      BY <2>3, <1>0 DEF MsgInv
    <2>5. b2 \in 0..(b1-1)
      BY <1>3, <1>7
    <2>6. PICK Q3 \in Quorums :
            \A a \in Q3 : VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
      BY <2>4, <2>5 DEF SafeAt
    <2>7. PICK a \in Q2 \cap Q3 : TRUE
      BY QuorumAssumption
    <2>8. VotedForIn(a, v2, b2)
      BY <1>2b, <2>7
    <2>9. VotedForIn(a, v1, b2) \/ WontVoteIn(a, b2)
      BY <2>6, <2>7
    <2>10. ~ WontVoteIn(a, b2)
      BY <2>8 DEF WontVoteIn
    <2>11. VotedForIn(a, v1, b2)
      BY <2>9, <2>10
    <2>12. QED BY <2>8, <2>11, Votes_Unique, <1>0
  <1>8. QED BY <1>3, <1>5, <1>6, <1>7

LEMMA L_Init == Init => IndInv
PROOF
  <1> SUFFICES ASSUME Init PROVE TypeOK /\ MsgInv /\ AccInv
    BY DEF IndInv
  <1> USE DEF Init
  <1>1. TypeOK
    BY DEF TypeOK, Messages, Ballots
  <1>2. MsgInv
    BY DEF MsgInv
  <1>3. AccInv
    BY DEF AccInv, Ballots, VotedForIn
  <1>4. QED BY <1>1, <1>2, <1>3

LEMMA L_Phase1a ==
  ASSUME IndInv, NEW bb \in Ballots, Phase1a(bb)
  PROVE IndInv'
PROOF
  <1> USE QuorumAssumption DEF IndInv, TypeOK, AccInv, MsgInv
  <1>. DEFINE newm == [type |-> "1a", bal |-> bb]
  <1>1. msgs' = msgs \cup {newm}
    BY DEF Phase1a, Send
  <1>2. newm \in Messages
    BY DEF Messages
  <1>3. maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
    BY DEF Phase1a
  <1>5. \A aa, vv, cc : VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
    <2>1. SUFFICES ASSUME NEW aa, NEW vv, NEW cc
                   PROVE VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
      OBVIOUS
    <2>2. ASSUME VotedForIn(aa, vv, cc) PROVE VotedForIn(aa, vv, cc)'
      <3>1. PICK mm \in msgs :
              mm.type = "2b" /\ mm.val = vv /\ mm.bal = cc /\ mm.acc = aa
        BY <2>2 DEF VotedForIn
      <3>2. QED BY <3>1, <1>1 DEF VotedForIn
    <2>3. ASSUME VotedForIn(aa, vv, cc)' PROVE VotedForIn(aa, vv, cc)
      <3>1. PICK mm \in msgs' :
              mm.type = "2b" /\ mm.val = vv /\ mm.bal = cc /\ mm.acc = aa
        BY <2>3 DEF VotedForIn
      <3>2. mm # newm BY <3>1 DEF newm
      <3>3. mm \in msgs BY <3>1, <3>2, <1>1
      <3>4. QED BY <3>1, <3>3 DEF VotedForIn
    <2>4. QED BY <2>2, <2>3
  <1>6. \A aa, cc : WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
    BY <1>3, <1>5 DEF WontVoteIn
  <1>7. \A vv, bb1 : SafeAt(vv, bb1)' <=> SafeAt(vv, bb1)
    BY <1>5, <1>6 DEF SafeAt
  <1>10. TypeOK'
    BY <1>1, <1>2, <1>3 DEF TypeOK
  <1>11. MsgInv'
    <2> SUFFICES ASSUME NEW m \in msgs'
                 PROVE
                   /\ (m.type = "1b") =>
                        /\ m.bal =< maxBal'[m.acc]
                        /\ \/ m.maxVBal = -1
                           \/ /\ m.maxVBal \in 0..(m.bal - 1)
                              /\ m.maxVal \in Values
                              /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                        /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                             \A v \in Values : ~ VotedForIn(m.acc, v, b1)'
                   /\ (m.type = "2a") =>
                        /\ SafeAt(m.val, m.bal)'
                        /\ \A m2 \in msgs' :
                             (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
                   /\ (m.type = "2b") =>
                        \E m2 \in msgs' : /\ m2.type = "2a"
                                          /\ m2.bal = m.bal
                                          /\ m2.val = m.val
      BY DEF MsgInv
    <2>1. CASE m = newm
      <3>1. m.type = "1a" BY <2>1 DEF newm
      <3>2. QED BY <3>1
    <2>2. CASE m \in msgs
      <3>1. m \in Messages BY <2>2 DEF TypeOK
      <3>2. /\ (m.type = "1b") =>
                /\ m.bal =< maxBal[m.acc]
                /\ \/ m.maxVBal = -1
                   \/ /\ m.maxVBal \in 0..(m.bal - 1)
                      /\ m.maxVal \in Values
                      /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                     \A v \in Values : ~ VotedForIn(m.acc, v, b1)
            /\ (m.type = "2a") =>
                /\ SafeAt(m.val, m.bal)
                /\ \A m2 \in msgs :
                     (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
            /\ (m.type = "2b") =>
                 \E m2 \in msgs : /\ m2.type = "2a"
                                  /\ m2.bal = m.bal
                                  /\ m2.val = m.val
        BY <2>2 DEF MsgInv
      <3>3. ASSUME m.type = "1b" PROVE
              /\ m.bal =< maxBal'[m.acc]
              /\ \/ m.maxVBal = -1
                 \/ /\ m.maxVBal \in 0..(m.bal - 1)
                    /\ m.maxVal \in Values
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                   \A v \in Values : ~ VotedForIn(m.acc, v, b1)'
        <4>1. m \in [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                     maxVal : Values \cup {None}, acc : Acceptors]
          BY <3>1, <3>3 DEF Messages
        <4>2. m.acc \in Acceptors /\ m.bal \in Ballots /\
              m.maxVBal \in Ballots \cup {-1} /\ m.maxVal \in Values \cup {None}
          BY <4>1
        <4>3. /\ m.bal =< maxBal[m.acc]
              /\ \/ m.maxVBal = -1
                 \/ /\ m.maxVBal \in 0..(m.bal - 1)
                    /\ m.maxVal \in Values
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
              /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                   \A v \in Values : ~ VotedForIn(m.acc, v, b1)
          BY <3>2, <3>3
        <4>4. m.bal =< maxBal'[m.acc] BY <4>3, <1>3
        <4>5. \/ m.maxVBal = -1
              \/ /\ m.maxVBal \in 0..(m.bal - 1)
                 /\ m.maxVal \in Values
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
          <5>1. CASE m.maxVBal = -1 BY <5>1
          <5>2. CASE m.maxVBal \in 0..(m.bal - 1) /\ m.maxVal \in Values
                       /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            <6>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              BY <5>2, <1>5
            <6>2. QED BY <5>2, <6>1
          <5>3. QED BY <4>3, <5>1, <5>2
        <4>6. \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                \A v \in Values : ~ VotedForIn(m.acc, v, b1)'
          <5>1. SUFFICES ASSUME NEW b1 \in (m.maxVBal + 1)..(m.bal - 1),
                                 NEW v \in Values
                         PROVE ~ VotedForIn(m.acc, v, b1)'
            OBVIOUS
          <5>2. ~ VotedForIn(m.acc, v, b1) BY <5>1, <4>3
          <5>3. QED BY <5>2, <1>5
        <4>7. QED BY <4>4, <4>5, <4>6
      <3>4. ASSUME m.type = "2a" PROVE
              /\ SafeAt(m.val, m.bal)'
              /\ \A m2 \in msgs' :
                   (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
        <4>1. m \in [type : {"2a"}, bal : Ballots, val : Values]
          BY <3>1, <3>4 DEF Messages
        <4>2. SafeAt(m.val, m.bal) /\
              (\A m2 \in msgs :
                 (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val))
          BY <3>2, <3>4
        <4>3. SafeAt(m.val, m.bal)' BY <4>2, <1>7
        <4>4. \A m2 \in msgs' :
                (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
          <5>1. SUFFICES ASSUME NEW m2 \in msgs', m2.type = "2a", m2.bal = m.bal
                         PROVE m2.val = m.val
            OBVIOUS
          <5>2. m2 # newm BY <5>1 DEF newm
          <5>3. m2 \in msgs BY <5>1, <5>2, <1>1
          <5>4. QED BY <5>3, <5>1, <4>2
        <4>5. QED BY <4>3, <4>4
      <3>5. ASSUME m.type = "2b" PROVE
              \E m2 \in msgs' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
        <4>1. \E m2 \in msgs : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
          BY <3>2, <3>5
        <4>2. QED BY <4>1, <1>1
      <3>6. QED BY <3>3, <3>4, <3>5
    <2>3. QED BY <2>1, <2>2, <1>1
  <1>12. AccInv'
    <2> SUFFICES ASSUME NEW a \in Acceptors PROVE
          /\ maxBal'[a] >= maxVBal'[a]
          /\ (maxVBal'[a] # -1) =>
                /\ maxVBal'[a] \in Nat
                /\ maxVal'[a] \in Values
                /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                       /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          /\ \A v \in Values, b \in Ballots :
                VotedForIn(a, v, b)' => maxVBal'[a] >= b
      BY DEF AccInv
    <2>1. maxBal'[a] = maxBal[a] /\ maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
      BY <1>3
    <2>2. /\ maxBal[a] >= maxVBal[a]
          /\ ((maxVBal[a] # -1) =>
                  /\ maxVBal[a] \in Nat
                  /\ maxVal[a] \in Values
                  /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                         /\ mm.bal = maxVBal[a] /\ mm.acc = a)
          /\ (\A v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => maxVBal[a] >= b)
      BY DEF AccInv
    <2>3. maxBal'[a] >= maxVBal'[a] BY <2>1, <2>2
    <2>4. (maxVBal'[a] # -1) =>
            /\ maxVBal'[a] \in Nat
            /\ maxVal'[a] \in Values
            /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                    /\ mm.bal = maxVBal'[a] /\ mm.acc = a
      <3>1. ASSUME maxVBal'[a] # -1 PROVE
              /\ maxVBal'[a] \in Nat
              /\ maxVal'[a] \in Values
              /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                     /\ mm.bal = maxVBal'[a] /\ mm.acc = a
        <4>1. maxVBal[a] # -1 BY <3>1, <2>1
        <4>2. /\ maxVBal[a] \in Nat
              /\ maxVal[a] \in Values
              /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                     /\ mm.bal = maxVBal[a] /\ mm.acc = a
          BY <4>1, <2>2
        <4>3. \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                  /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          BY <4>2, <2>1, <1>1
        <4>4. QED BY <4>2, <4>3, <2>1
      <3>2. QED BY <3>1
    <2>5. \A v \in Values, b \in Ballots :
            VotedForIn(a, v, b)' => maxVBal'[a] >= b
      <3>1. SUFFICES ASSUME NEW v \in Values, NEW b \in Ballots, VotedForIn(a, v, b)'
                     PROVE maxVBal'[a] >= b
        OBVIOUS
      <3>2. VotedForIn(a, v, b) BY <3>1, <1>5
      <3>3. maxVBal[a] >= b BY <3>2, <2>2
      <3>4. QED BY <3>3, <2>1
    <2>6. QED BY <2>3, <2>4, <2>5
  <1>13. QED BY <1>10, <1>11, <1>12 DEF IndInv

LEMMA L_Phase1b ==
  ASSUME IndInv, NEW ax \in Acceptors, Phase1b(ax)
  PROVE IndInv'
PROOF
  <1> USE QuorumAssumption DEF IndInv, TypeOK, AccInv, MsgInv
  <1>0. PICK m1a \in msgs :
          /\ m1a.type = "1a"
          /\ m1a.bal > maxBal[ax]
          /\ maxBal' = [maxBal EXCEPT ![ax] = m1a.bal]
          /\ msgs' = msgs \cup {[type |-> "1b", bal |-> m1a.bal,
                                  maxVBal |-> maxVBal[ax], maxVal |-> maxVal[ax],
                                  acc |-> ax]}
          /\ maxVBal' = maxVBal
          /\ maxVal' = maxVal
    BY DEF Phase1b, Send
  <1>. DEFINE newm == [type |-> "1b", bal |-> m1a.bal,
                maxVBal |-> maxVBal[ax], maxVal |-> maxVal[ax], acc |-> ax]
  <1>1. msgs' = msgs \cup {newm}
    BY <1>0 DEF newm
  <1>2. m1a.bal \in Ballots
    <2>1. m1a \in Messages BY <1>0 DEF TypeOK
    <2>2. m1a \in [type : {"1a"}, bal : Ballots]
      BY <2>1, <1>0 DEF Messages
    <2>3. QED BY <2>2
  <1>3. maxVBal[ax] \in Ballots \cup {-1} /\ maxVal[ax] \in Values \cup {None}
    BY DEF TypeOK
  <1>4. newm \in Messages
    BY <1>2, <1>3 DEF newm, Messages
  <1>5. maxBal'[ax] = m1a.bal
    BY <1>0, <1>2 DEF TypeOK
  <1>6. \A a \in Acceptors : a # ax => maxBal'[a] = maxBal[a]
    BY <1>0, <1>2 DEF TypeOK
  <1>7. maxBal' \in [Acceptors -> Ballots \cup {-1}]
    BY <1>0, <1>2 DEF TypeOK
  <1>8. maxVBal' = maxVBal /\ maxVal' = maxVal
    BY <1>0
  <1>9. \A aa, vv, cc : VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
    <2>1. SUFFICES ASSUME NEW aa, NEW vv, NEW cc
                   PROVE VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
      OBVIOUS
    <2>2. ASSUME VotedForIn(aa, vv, cc) PROVE VotedForIn(aa, vv, cc)'
      <3>1. PICK mm \in msgs :
              mm.type = "2b" /\ mm.val = vv /\ mm.bal = cc /\ mm.acc = aa
        BY <2>2 DEF VotedForIn
      <3>2. QED BY <3>1, <1>1 DEF VotedForIn
    <2>3. ASSUME VotedForIn(aa, vv, cc)' PROVE VotedForIn(aa, vv, cc)
      <3>1. PICK mm \in msgs' :
              mm.type = "2b" /\ mm.val = vv /\ mm.bal = cc /\ mm.acc = aa
        BY <2>3 DEF VotedForIn
      <3>2. mm # newm BY <3>1 DEF newm
      <3>3. mm \in msgs BY <3>1, <3>2, <1>1
      <3>4. QED BY <3>1, <3>3 DEF VotedForIn
    <2>4. QED BY <2>2, <2>3
  <1>10. \A a \in Acceptors, c \in Nat : WontVoteIn(a, c) => WontVoteIn(a, c)'
    <2>1. SUFFICES ASSUME NEW a \in Acceptors, NEW c \in Nat, WontVoteIn(a, c)
                   PROVE WontVoteIn(a, c)'
      OBVIOUS
    <2>2. (\A v \in Values : ~ VotedForIn(a, v, c)) /\ maxBal[a] > c
      BY <2>1 DEF WontVoteIn
    <2>3. \A v \in Values : ~ VotedForIn(a, v, c)'
      <3>1. SUFFICES ASSUME NEW v \in Values PROVE ~ VotedForIn(a, v, c)'
        OBVIOUS
      <3>2. ~ VotedForIn(a, v, c) BY <2>2
      <3>3. QED BY <3>2, <1>9
    <2>4. maxBal'[a] > c
      <3>1. maxBal[a] > c BY <2>2
      <3>0. maxBal[a] \in Ballots \cup {-1} BY DEF TypeOK
      <3>0a. maxBal[a] \in Nat BY <3>1, <3>0 DEF Ballots
      <3>2. CASE a = ax
        <4>1. maxBal'[a] = m1a.bal BY <3>2, <1>5
        <4>2. m1a.bal > maxBal[ax] BY <1>0
        <4>3. m1a.bal > maxBal[a] BY <4>2, <3>2
        <4>4. m1a.bal > c BY <4>3, <3>1, <3>0a, <1>2 DEF Ballots
        <4>5. QED BY <4>1, <4>4
      <3>3. CASE a # ax
        <4>1. maxBal'[a] = maxBal[a] BY <3>3, <1>6
        <4>2. QED BY <4>1, <3>1
      <3>4. QED BY <3>2, <3>3
    <2>5. QED BY <2>3, <2>4 DEF WontVoteIn
  <1>11. \A v \in Values, b \in Nat : SafeAt(v, b) => SafeAt(v, b)'
    <2>1. SUFFICES ASSUME NEW v \in Values, NEW b \in Nat, SafeAt(v, b)
                   PROVE SafeAt(v, b)'
      OBVIOUS
    <2>2. SUFFICES ASSUME NEW c \in 0..(b-1)
                   PROVE \E Q \in Quorums :
                            \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
      BY DEF SafeAt
    <2>3. PICK Q \in Quorums :
            \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
      BY <2>1, <2>2 DEF SafeAt
    <2>4. \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
      <3>1. SUFFICES ASSUME NEW a \in Q
                     PROVE VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
        OBVIOUS
      <3>2. a \in Acceptors BY <3>1, QuorumAssumption
      <3>3. c \in Nat BY <2>2
      <3>4. VotedForIn(a, v, c) \/ WontVoteIn(a, c) BY <2>3, <3>1
      <3>5. CASE VotedForIn(a, v, c) BY <3>5, <1>9
      <3>6. CASE WontVoteIn(a, c) BY <3>6, <1>10, <3>2, <3>3
      <3>7. QED BY <3>4, <3>5, <3>6
    <2>5. QED BY <2>4
  <1>20. TypeOK'
    BY <1>1, <1>4, <1>7, <1>8 DEF TypeOK
  <1>21. MsgInv'
    <2> SUFFICES ASSUME NEW m \in msgs'
                 PROVE
                   /\ (m.type = "1b") =>
                        /\ m.bal =< maxBal'[m.acc]
                        /\ \/ m.maxVBal = -1
                           \/ /\ m.maxVBal \in 0..(m.bal - 1)
                              /\ m.maxVal \in Values
                              /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                        /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                             \A v \in Values : ~ VotedForIn(m.acc, v, b1)'
                   /\ (m.type = "2a") =>
                        /\ SafeAt(m.val, m.bal)'
                        /\ \A m2 \in msgs' :
                             (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
                   /\ (m.type = "2b") =>
                        \E m2 \in msgs' : /\ m2.type = "2a"
                                          /\ m2.bal = m.bal
                                          /\ m2.val = m.val
      BY DEF MsgInv
    <2>1. CASE m = newm
      <3>1. m.type = "1b" /\ m.acc = ax /\ m.bal = m1a.bal
              /\ m.maxVBal = maxVBal[ax] /\ m.maxVal = maxVal[ax]
        BY <2>1 DEF newm
      <3>2. m.bal =< maxBal'[m.acc]
        BY <3>1, <1>5, <1>2 DEF Ballots
      <3>3. \/ m.maxVBal = -1
            \/ /\ m.maxVBal \in 0..(m.bal - 1)
               /\ m.maxVal \in Values
               /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
        <4>1. CASE maxVBal[ax] = -1
          BY <4>1, <3>1
        <4>2. CASE maxVBal[ax] # -1
          <5>1a. /\ maxVBal[ax] \in Nat
                 /\ maxVal[ax] \in Values
                 /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[ax]
                                       /\ mm.bal = maxVBal[ax] /\ mm.acc = ax
            BY <4>2 DEF AccInv
          <5>1. /\ maxVBal[ax] \in Nat
                /\ maxVal[ax] \in Values
                /\ VotedForIn(ax, maxVal[ax], maxVBal[ax])
            BY <5>1a DEF VotedForIn
          <5>2. maxBal[ax] >= maxVBal[ax] BY DEF AccInv
          <5>3. m1a.bal > maxBal[ax] BY <1>0
          <5>4. m1a.bal > maxVBal[ax]
            <6>1. maxBal[ax] \in Ballots \cup {-1} BY DEF TypeOK
            <6>2. maxBal[ax] \in Nat BY <5>2, <6>1, <5>1 DEF Ballots
            <6>3. QED BY <5>2, <5>3, <5>1, <6>2, <1>2 DEF Ballots
          <5>5. m.maxVBal \in 0..(m.bal - 1)
            <6>1. maxVBal[ax] \in 0..(m1a.bal - 1)
              BY <5>1, <5>4, <1>2 DEF Ballots
            <6>2. QED BY <3>1, <6>1
          <5>6. m.maxVal \in Values BY <5>1, <3>1
          <5>7. VotedForIn(m.acc, m.maxVal, m.maxVBal)'
            BY <5>1, <1>9, <3>1
          <5>8. QED BY <5>5, <5>6, <5>7
        <4>3. QED BY <4>1, <4>2
      <3>4. \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
              \A v \in Values : ~ VotedForIn(m.acc, v, b1)'
        <4>1. SUFFICES ASSUME NEW b1 \in (m.maxVBal + 1)..(m.bal - 1),
                               NEW v \in Values
                       PROVE ~ VotedForIn(m.acc, v, b1)'
          OBVIOUS
        <4>2. m.maxVBal = maxVBal[ax] BY <3>1
        <4>3. maxVBal[ax] \in Ballots \cup {-1} BY DEF TypeOK
        <4>4. m.maxVBal + 1 \in Nat
          BY <4>2, <4>3 DEF Ballots
        <4>5. b1 \in Nat BY <4>1, <4>4
        <4>6. b1 > maxVBal[ax]
          <5>1. b1 >= m.maxVBal + 1 BY <4>1
          <5>2. b1 > m.maxVBal
            <6>1. CASE m.maxVBal = -1
              BY <5>1, <4>5, <6>1
            <6>2. CASE m.maxVBal # -1
              <7>1. m.maxVBal \in Nat BY <4>2, <4>3, <6>2 DEF Ballots, TypeOK
              <7>2. QED BY <5>1, <4>5, <7>1
            <6>3. QED BY <4>2, <4>3, <6>1, <6>2 DEF Ballots
          <5>3. QED BY <5>2, <4>2
        <4>7. ~ VotedForIn(ax, v, b1)
          <5>1. ASSUME VotedForIn(ax, v, b1) PROVE FALSE
            <6>1. b1 \in Ballots BY <4>5 DEF Ballots
            <6>2. maxVBal[ax] >= b1 BY <5>1, <6>1 DEF AccInv
            <6>3. QED BY <6>2, <4>6
          <5>2. QED BY <5>1
        <4>8. QED BY <4>7, <1>9, <3>1
      <3>5. QED BY <3>1, <3>2, <3>3, <3>4
    <2>2. CASE m \in msgs
      <3>1. m \in Messages BY <2>2 DEF TypeOK
      <3>2. /\ (m.type = "1b") =>
                /\ m.bal =< maxBal[m.acc]
                /\ \/ m.maxVBal = -1
                   \/ /\ m.maxVBal \in 0..(m.bal - 1)
                      /\ m.maxVal \in Values
                      /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                     \A v \in Values : ~ VotedForIn(m.acc, v, b1)
            /\ (m.type = "2a") =>
                /\ SafeAt(m.val, m.bal)
                /\ \A m2 \in msgs :
                     (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
            /\ (m.type = "2b") =>
                 \E m2 \in msgs : /\ m2.type = "2a"
                                  /\ m2.bal = m.bal
                                  /\ m2.val = m.val
        BY <2>2 DEF MsgInv
      <3>3. ASSUME m.type = "1b" PROVE
              /\ m.bal =< maxBal'[m.acc]
              /\ \/ m.maxVBal = -1
                 \/ /\ m.maxVBal \in 0..(m.bal - 1)
                    /\ m.maxVal \in Values
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                   \A v \in Values : ~ VotedForIn(m.acc, v, b1)'
        <4>1. m \in [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                     maxVal : Values \cup {None}, acc : Acceptors]
          BY <3>1, <3>3 DEF Messages
        <4>2. m.acc \in Acceptors /\ m.bal \in Ballots /\
              m.maxVBal \in Ballots \cup {-1} /\ m.maxVal \in Values \cup {None}
          BY <4>1
        <4>3. /\ m.bal =< maxBal[m.acc]
              /\ \/ m.maxVBal = -1
                 \/ /\ m.maxVBal \in 0..(m.bal - 1)
                    /\ m.maxVal \in Values
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
              /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                   \A v \in Values : ~ VotedForIn(m.acc, v, b1)
          BY <3>2, <3>3
        <4>4. m.bal =< maxBal'[m.acc]
          <5>1. CASE m.acc = ax
            <6>1. maxBal'[m.acc] = m1a.bal BY <1>5, <5>1
            <6>2. m1a.bal > maxBal[ax] BY <1>0
            <6>3. m.bal =< maxBal[ax] BY <4>3, <5>1
            <6>3a. maxBal[ax] \in Ballots \cup {-1} BY DEF TypeOK
            <6>3b. maxBal[ax] \in Nat BY <6>3, <6>3a, <4>2 DEF Ballots
            <6>4. m.bal =< m1a.bal BY <6>2, <6>3, <6>3b, <4>2, <1>2 DEF Ballots
            <6>5. QED BY <6>4, <6>1
          <5>2. CASE m.acc # ax
            <6>1. maxBal'[m.acc] = maxBal[m.acc] BY <1>6, <5>2, <4>2
            <6>2. QED BY <6>1, <4>3
          <5>3. QED BY <5>1, <5>2
        <4>5. \/ m.maxVBal = -1
              \/ /\ m.maxVBal \in 0..(m.bal - 1)
                 /\ m.maxVal \in Values
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
          <5>1. CASE m.maxVBal = -1 BY <5>1
          <5>2. CASE m.maxVBal \in 0..(m.bal - 1) /\ m.maxVal \in Values
                       /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            <6>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' BY <5>2, <1>9
            <6>2. QED BY <5>2, <6>1
          <5>3. QED BY <4>3, <5>1, <5>2
        <4>6. \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                \A v \in Values : ~ VotedForIn(m.acc, v, b1)'
          <5>1. SUFFICES ASSUME NEW b1 \in (m.maxVBal + 1)..(m.bal - 1),
                                 NEW v \in Values
                         PROVE ~ VotedForIn(m.acc, v, b1)'
            OBVIOUS
          <5>2. ~ VotedForIn(m.acc, v, b1) BY <5>1, <4>3
          <5>3. QED BY <5>2, <1>9
        <4>7. QED BY <4>4, <4>5, <4>6
      <3>4. ASSUME m.type = "2a" PROVE
              /\ SafeAt(m.val, m.bal)'
              /\ \A m2 \in msgs' :
                   (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
        <4>1. m \in [type : {"2a"}, bal : Ballots, val : Values]
          BY <3>1, <3>4 DEF Messages
        <4>2. m.val \in Values /\ m.bal \in Ballots BY <4>1
        <4>3. m.bal \in Nat BY <4>2 DEF Ballots
        <4>4. SafeAt(m.val, m.bal) /\
              (\A m2 \in msgs :
                 (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val))
          BY <3>2, <3>4
        <4>5. SafeAt(m.val, m.bal)' BY <4>4, <1>11, <4>2, <4>3
        <4>6. \A m2 \in msgs' :
                (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
          <5>1. SUFFICES ASSUME NEW m2 \in msgs', m2.type = "2a", m2.bal = m.bal
                         PROVE m2.val = m.val
            OBVIOUS
          <5>2. m2 # newm BY <5>1 DEF newm
          <5>3. m2 \in msgs BY <5>1, <5>2, <1>1
          <5>4. QED BY <5>3, <5>1, <4>4
        <4>7. QED BY <4>5, <4>6
      <3>5. ASSUME m.type = "2b" PROVE
              \E m2 \in msgs' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
        <4>1. \E m2 \in msgs : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
          BY <3>2, <3>5
        <4>2. QED BY <4>1, <1>1
      <3>6. QED BY <3>3, <3>4, <3>5
    <2>3. QED BY <2>1, <2>2, <1>1
  <1>22. AccInv'
    <2> SUFFICES ASSUME NEW a \in Acceptors PROVE
          /\ maxBal'[a] >= maxVBal'[a]
          /\ (maxVBal'[a] # -1) =>
                /\ maxVBal'[a] \in Nat
                /\ maxVal'[a] \in Values
                /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                       /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          /\ \A v \in Values, b \in Ballots :
                VotedForIn(a, v, b)' => maxVBal'[a] >= b
      BY DEF AccInv
    <2>1. maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
      BY <1>8
    <2>2. /\ maxBal[a] >= maxVBal[a]
          /\ ((maxVBal[a] # -1) =>
                /\ maxVBal[a] \in Nat
                /\ maxVal[a] \in Values
                /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                       /\ mm.bal = maxVBal[a] /\ mm.acc = a)
          /\ (\A v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => maxVBal[a] >= b)
      BY DEF AccInv
    <2>3. maxBal'[a] >= maxBal[a]
      <3>0. maxBal[a] \in Ballots \cup {-1} BY DEF TypeOK
      <3>1. CASE a = ax
        <4>1. maxBal'[a] = m1a.bal BY <1>5, <3>1
        <4>2. m1a.bal > maxBal[ax] BY <1>0
        <4>3. QED BY <4>1, <4>2, <3>1, <3>0, <1>2 DEF Ballots
      <3>2. CASE a # ax
        BY <3>2, <1>6, <3>0 DEF Ballots
      <3>3. QED BY <3>1, <3>2
    <2>4. maxBal'[a] >= maxVBal'[a]
      <3>1. maxBal[a] >= maxVBal[a] BY <2>2
      <3>2. maxBal'[a] >= maxBal[a] BY <2>3
      <3>3. maxVBal'[a] = maxVBal[a] BY <2>1
      <3>4. maxBal[a] \in Ballots \cup {-1} /\ maxVBal[a] \in Ballots \cup {-1}
        BY DEF TypeOK
      <3>5. maxBal'[a] \in Ballots \cup {-1} BY <1>7
      <3>6. QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Ballots
    <2>5. (maxVBal'[a] # -1) =>
            /\ maxVBal'[a] \in Nat
            /\ maxVal'[a] \in Values
            /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                    /\ mm.bal = maxVBal'[a] /\ mm.acc = a
      <3>1. ASSUME maxVBal'[a] # -1 PROVE
              /\ maxVBal'[a] \in Nat
              /\ maxVal'[a] \in Values
              /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                     /\ mm.bal = maxVBal'[a] /\ mm.acc = a
        <4>1. maxVBal[a] # -1 BY <3>1, <2>1
        <4>2. /\ maxVBal[a] \in Nat
              /\ maxVal[a] \in Values
              /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                     /\ mm.bal = maxVBal[a] /\ mm.acc = a
          BY <4>1, <2>2
        <4>3. \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                  /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          BY <4>2, <2>1, <1>1
        <4>4. QED BY <4>2, <4>3, <2>1
      <3>2. QED BY <3>1
    <2>6. \A v \in Values, b \in Ballots :
            VotedForIn(a, v, b)' => maxVBal'[a] >= b
      <3>1. SUFFICES ASSUME NEW v \in Values, NEW b \in Ballots, VotedForIn(a, v, b)'
                     PROVE maxVBal'[a] >= b
        OBVIOUS
      <3>2. VotedForIn(a, v, b) BY <3>1, <1>9
      <3>3. maxVBal[a] >= b BY <3>2, <2>2
      <3>4. QED BY <3>3, <2>1
    <2>7. QED BY <2>4, <2>5, <2>6
  <1>23. QED BY <1>20, <1>21, <1>22 DEF IndInv

LEMMA L_Phase2a ==
  ASSUME IndInv, NEW bb \in Ballots, Phase2a(bb)
  PROVE IndInv'
PROOF
  <1> USE QuorumAssumption DEF IndInv, TypeOK, AccInv, MsgInv
  <1>0. PICK v \in Values, Qx \in Quorums,
              Sx \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = bb)} :
                /\ \A a \in Qx : \E m \in Sx : m.acc = a
                /\ \/ \A m \in Sx : m.maxVBal = -1
                   \/ \E c \in 0..(bb-1) :
                         /\ \A m \in Sx : m.maxVBal =< c
                         /\ \E m \in Sx : /\ m.maxVBal = c
                                          /\ m.maxVal = v
                /\ msgs' = msgs \cup {[type |-> "2a", bal |-> bb, val |-> v]}
    BY DEF Phase2a, Send
  <1>. DEFINE newm == [type |-> "2a", bal |-> bb, val |-> v]
  <1>1. msgs' = msgs \cup {newm}
    BY <1>0 DEF newm
  <1>2. newm \in Messages
    BY <1>0 DEF newm, Messages
  <1>3. maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
    BY DEF Phase2a
  <1>5. \A aa, vv, cc : VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
    <2>1. SUFFICES ASSUME NEW aa, NEW vv, NEW cc
                   PROVE VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
      OBVIOUS
    <2>2. ASSUME VotedForIn(aa, vv, cc) PROVE VotedForIn(aa, vv, cc)'
      <3>1. PICK mm \in msgs :
              mm.type = "2b" /\ mm.val = vv /\ mm.bal = cc /\ mm.acc = aa
        BY <2>2 DEF VotedForIn
      <3>2. QED BY <3>1, <1>1 DEF VotedForIn
    <2>3. ASSUME VotedForIn(aa, vv, cc)' PROVE VotedForIn(aa, vv, cc)
      <3>1. PICK mm \in msgs' :
              mm.type = "2b" /\ mm.val = vv /\ mm.bal = cc /\ mm.acc = aa
        BY <2>3 DEF VotedForIn
      <3>2. mm # newm BY <3>1 DEF newm
      <3>3. mm \in msgs BY <3>1, <3>2, <1>1
      <3>4. QED BY <3>1, <3>3 DEF VotedForIn
    <2>4. QED BY <2>2, <2>3
  <1>6. \A aa, cc : WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
    BY <1>3, <1>5 DEF WontVoteIn
  <1>7. \A vv, bx : SafeAt(vv, bx)' <=> SafeAt(vv, bx)
    BY <1>5, <1>6 DEF SafeAt
  <1>8. ~ \E m \in msgs : m.type = "2a" /\ m.bal = bb
    BY DEF Phase2a
  <1>9. SafeAt(v, bb)
    <2>1. SUFFICES ASSUME NEW c2 \in 0..(bb-1)
                   PROVE \E Q \in Quorums :
                            \A a \in Q : VotedForIn(a, v, c2) \/ WontVoteIn(a, c2)
      BY DEF SafeAt
    <2>2. c2 \in Nat /\ c2 < bb BY <2>1 DEF Ballots
    <2>3. CASE \A m \in Sx : m.maxVBal = -1
      <3>1. SUFFICES \A a \in Qx : VotedForIn(a, v, c2) \/ WontVoteIn(a, c2)
        BY <1>0
      <3>2. SUFFICES ASSUME NEW a \in Qx
                     PROVE VotedForIn(a, v, c2) \/ WontVoteIn(a, c2)
        OBVIOUS
      <3>3. PICK m_a \in Sx : m_a.acc = a BY <1>0
      <3>4. m_a \in msgs /\ m_a.type = "1b" /\ m_a.bal = bb BY <1>0, <3>3
      <3>5. m_a.maxVBal = -1 BY <2>3, <3>3
      <3>6. m_a \in [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                      maxVal : Values \cup {None}, acc : Acceptors]
        BY <3>4 DEF Messages, TypeOK
      <3>7. m_a.acc \in Acceptors BY <3>6
      <3>8. a \in Acceptors BY <3>3, <3>7
      <3>9. /\ m_a.bal =< maxBal[m_a.acc]
            /\ \A b1 \in (m_a.maxVBal + 1)..(m_a.bal - 1) :
                 \A v0 \in Values : ~ VotedForIn(m_a.acc, v0, b1)
        BY <3>4 DEF MsgInv
      <3>10. maxBal[a] >= bb BY <3>9, <3>4, <3>3
      <3>11. maxBal[a] > c2 BY <3>10, <2>2 DEF Ballots, TypeOK
      <3>12. \A v0 \in Values : ~ VotedForIn(a, v0, c2)
        <4>1. SUFFICES ASSUME NEW v0 \in Values PROVE ~ VotedForIn(a, v0, c2)
          OBVIOUS
        <4>2. m_a.maxVBal + 1 = 0 BY <3>5
        <4>3. c2 \in (m_a.maxVBal + 1)..(m_a.bal - 1)
          BY <4>2, <3>4, <2>2
        <4>4. ~ VotedForIn(m_a.acc, v0, c2) BY <4>3, <3>9
        <4>5. QED BY <4>4, <3>3
      <3>13. WontVoteIn(a, c2) BY <3>11, <3>12 DEF WontVoteIn
      <3>14. QED BY <3>13
    <2>4. CASE \E c \in 0..(bb-1) :
                  /\ \A m \in Sx : m.maxVBal =< c
                  /\ \E m \in Sx : /\ m.maxVBal = c
                                   /\ m.maxVal = v
      <3>1. PICK c \in 0..(bb-1) :
              /\ \A m \in Sx : m.maxVBal =< c
              /\ \E m \in Sx : m.maxVBal = c /\ m.maxVal = v
        BY <2>4
      <3>2. PICK m_a0 \in Sx : m_a0.maxVBal = c /\ m_a0.maxVal = v
        BY <3>1
      <3>3. c \in Nat /\ c < bb /\ c >= 0 BY <3>1 DEF Ballots
      <3>4. m_a0 \in msgs /\ m_a0.type = "1b" /\ m_a0.bal = bb
        BY <1>0, <3>2
      <3>5. m_a0 \in [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                      maxVal : Values \cup {None}, acc : Acceptors]
        BY <3>4 DEF Messages, TypeOK
      <3>6. m_a0.acc \in Acceptors BY <3>5
      <3>7. \/ m_a0.maxVBal = -1
            \/ /\ m_a0.maxVBal \in 0..(m_a0.bal - 1)
               /\ m_a0.maxVal \in Values
               /\ VotedForIn(m_a0.acc, m_a0.maxVal, m_a0.maxVBal)
        BY <3>4 DEF MsgInv
      <3>8. m_a0.maxVBal # -1 BY <3>2, <3>3
      <3>9. m_a0.maxVal \in Values /\ VotedForIn(m_a0.acc, m_a0.maxVal, m_a0.maxVBal)
        BY <3>7, <3>8
      <3>10. VotedForIn(m_a0.acc, v, c) BY <3>2, <3>9
      <3>11. c \in Ballots BY <3>3 DEF Ballots
      <3>12. \E m2a_c \in msgs : m2a_c.type = "2a" /\ m2a_c.bal = c /\ m2a_c.val = v
        BY Voted_Implies_2a, <3>10, <3>6, <3>11, <1>0 DEF MsgInv
      <3>13. PICK m2a_c \in msgs :
              m2a_c.type = "2a" /\ m2a_c.bal = c /\ m2a_c.val = v
        BY <3>12
      <3>14. SafeAt(v, c) BY <3>13 DEF MsgInv
      <3>15. CASE c2 = c
        <4>1. SUFFICES \A a \in Qx : VotedForIn(a, v, c2) \/ WontVoteIn(a, c2)
          BY <1>0
        <4>2. SUFFICES ASSUME NEW a \in Qx
                       PROVE VotedForIn(a, v, c2) \/ WontVoteIn(a, c2)
          OBVIOUS
        <4>3. PICK m_a \in Sx : m_a.acc = a BY <1>0
        <4>4. m_a \in msgs /\ m_a.type = "1b" /\ m_a.bal = bb
          BY <1>0, <4>3
        <4>5. m_a.maxVBal =< c BY <3>1, <4>3
        <4>6. m_a \in [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                       maxVal : Values \cup {None}, acc : Acceptors]
          BY <4>4 DEF Messages, TypeOK
        <4>7. m_a.acc \in Acceptors /\ m_a.maxVBal \in Ballots \cup {-1}
          BY <4>6
        <4>8. a \in Acceptors BY <4>3, <4>7
        <4>9. /\ m_a.bal =< maxBal[m_a.acc]
              /\ \/ m_a.maxVBal = -1
                 \/ /\ m_a.maxVBal \in 0..(m_a.bal - 1)
                    /\ m_a.maxVal \in Values
                    /\ VotedForIn(m_a.acc, m_a.maxVal, m_a.maxVBal)
              /\ \A b1 \in (m_a.maxVBal + 1)..(m_a.bal - 1) :
                   \A v0 \in Values : ~ VotedForIn(m_a.acc, v0, b1)
          BY <4>4 DEF MsgInv
        <4>10. maxBal[a] >= bb BY <4>9, <4>4, <4>3
        <4>11. maxBal[a] > c2 BY <4>10, <2>2 DEF Ballots, TypeOK
        <4>12. CASE m_a.maxVBal = c
          <5>1. m_a.maxVBal # -1 BY <4>12, <3>3
          <5>2. /\ m_a.maxVal \in Values
                /\ VotedForIn(m_a.acc, m_a.maxVal, m_a.maxVBal)
            BY <4>9, <5>1
          <5>3. VotedForIn(m_a.acc, m_a.maxVal, c) BY <5>2, <4>12
          <5>4. \E m2a_ma \in msgs :
                  m2a_ma.type = "2a" /\ m2a_ma.bal = c /\ m2a_ma.val = m_a.maxVal
            BY Voted_Implies_2a, <5>3, <4>7, <3>11, <5>2 DEF MsgInv
          <5>5. PICK m2a_ma \in msgs :
                  m2a_ma.type = "2a" /\ m2a_ma.bal = c /\ m2a_ma.val = m_a.maxVal
            BY <5>4
          <5>6. m_a.maxVal = v
            BY <5>5, <3>13, TwoA_Unique DEF MsgInv
          <5>7. VotedForIn(a, v, c) BY <5>3, <5>6, <4>3
          <5>8. QED BY <5>7, <3>15
        <4>13. CASE m_a.maxVBal < c
          <5>1. c \in (m_a.maxVBal + 1)..(m_a.bal - 1)
            <6>1. m_a.maxVBal + 1 =< c
              <7>1. CASE m_a.maxVBal = -1
                BY <7>1, <3>3
              <7>2. CASE m_a.maxVBal # -1
                <8>1. m_a.maxVBal \in Nat BY <4>7, <7>2 DEF Ballots
                <8>2. QED BY <8>1, <4>13, <3>3
              <7>3. QED BY <4>7, <7>1, <7>2
            <6>2. c =< m_a.bal - 1
              BY <4>4, <3>3
            <6>3. QED BY <6>1, <6>2
          <5>2. \A v0 \in Values : ~ VotedForIn(a, v0, c)
            <6>1. SUFFICES ASSUME NEW v0 \in Values PROVE ~ VotedForIn(a, v0, c)
              OBVIOUS
            <6>2. ~ VotedForIn(m_a.acc, v0, c) BY <5>1, <4>9
            <6>3. QED BY <6>2, <4>3
          <5>3. WontVoteIn(a, c) BY <5>2, <4>11, <3>15 DEF WontVoteIn
          <5>4. QED BY <5>3, <3>15
        <4>14. QED BY <4>5, <4>12, <4>13
      <3>16. CASE c < c2
        <4>1. SUFFICES \A a \in Qx : VotedForIn(a, v, c2) \/ WontVoteIn(a, c2)
          BY <1>0
        <4>2. SUFFICES ASSUME NEW a \in Qx
                       PROVE VotedForIn(a, v, c2) \/ WontVoteIn(a, c2)
          OBVIOUS
        <4>3. PICK m_a \in Sx : m_a.acc = a BY <1>0
        <4>4. m_a \in msgs /\ m_a.type = "1b" /\ m_a.bal = bb
          BY <1>0, <4>3
        <4>5. m_a.maxVBal =< c BY <3>1, <4>3
        <4>6. m_a \in [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                       maxVal : Values \cup {None}, acc : Acceptors]
          BY <4>4 DEF Messages, TypeOK
        <4>7. m_a.acc \in Acceptors /\ m_a.maxVBal \in Ballots \cup {-1}
          BY <4>6
        <4>8. a \in Acceptors BY <4>3, <4>7
        <4>9. /\ m_a.bal =< maxBal[m_a.acc]
              /\ \A b1 \in (m_a.maxVBal + 1)..(m_a.bal - 1) :
                   \A v0 \in Values : ~ VotedForIn(m_a.acc, v0, b1)
          BY <4>4 DEF MsgInv
        <4>10. maxBal[a] >= bb BY <4>9, <4>4, <4>3
        <4>11. maxBal[a] > c2 BY <4>10, <2>2 DEF Ballots, TypeOK
        <4>12. c2 \in (m_a.maxVBal + 1)..(m_a.bal - 1)
          <5>1. m_a.maxVBal + 1 =< c2
            <6>1. CASE m_a.maxVBal = -1
              BY <6>1, <2>2
            <6>2. CASE m_a.maxVBal # -1
              <7>1. m_a.maxVBal \in Nat BY <4>7, <6>2 DEF Ballots
              <7>2. QED BY <7>1, <4>5, <3>16, <3>3, <2>2
            <6>3. QED BY <4>7, <6>1, <6>2
          <5>2. c2 =< m_a.bal - 1
            BY <4>4, <2>2
          <5>3. QED BY <5>1, <5>2
        <4>13. \A v0 \in Values : ~ VotedForIn(a, v0, c2)
          <5>1. SUFFICES ASSUME NEW v0 \in Values PROVE ~ VotedForIn(a, v0, c2)
            OBVIOUS
          <5>2. ~ VotedForIn(m_a.acc, v0, c2) BY <4>12, <4>9
          <5>3. QED BY <5>2, <4>3
        <4>14. WontVoteIn(a, c2) BY <4>11, <4>13 DEF WontVoteIn
        <4>15. QED BY <4>14
      <3>17. CASE c2 < c
        <4>1. c2 \in 0..(c-1) BY <2>2, <3>17, <3>3
        <4>2. QED BY <3>14, <4>1 DEF SafeAt
      <3>18. QED BY <3>15, <3>16, <3>17, <2>2, <3>3
    <2>5. QED BY <2>3, <2>4, <1>0
  <1>10. TypeOK'
    BY <1>1, <1>2, <1>3 DEF TypeOK
  <1>11. MsgInv'
    <2> SUFFICES ASSUME NEW m \in msgs'
                 PROVE
                   /\ (m.type = "1b") =>
                        /\ m.bal =< maxBal'[m.acc]
                        /\ \/ m.maxVBal = -1
                           \/ /\ m.maxVBal \in 0..(m.bal - 1)
                              /\ m.maxVal \in Values
                              /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                        /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                             \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)'
                   /\ (m.type = "2a") =>
                        /\ SafeAt(m.val, m.bal)'
                        /\ \A m2 \in msgs' :
                             (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
                   /\ (m.type = "2b") =>
                        \E m2 \in msgs' : /\ m2.type = "2a"
                                          /\ m2.bal = m.bal
                                          /\ m2.val = m.val
      BY DEF MsgInv
    <2>1. CASE m = newm
      <3>1. m.type = "2a" /\ m.bal = bb /\ m.val = v BY <2>1 DEF newm
      <3>2. SafeAt(m.val, m.bal)'
        BY <1>9, <1>7, <1>0, <3>1
      <3>3. \A m2 \in msgs' :
              (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
        <4>1. SUFFICES ASSUME NEW m2 \in msgs', m2.type = "2a", m2.bal = m.bal
                       PROVE m2.val = m.val
          OBVIOUS
        <4>2. CASE m2 = newm
          BY <4>2, <3>1 DEF newm
        <4>3. CASE m2 \in msgs
          <5>1. m2 \in msgs /\ m2.type = "2a" /\ m2.bal = bb
            BY <4>3, <4>1, <3>1
          <5>2. QED BY <5>1, <1>8
        <4>4. QED BY <4>2, <4>3, <1>1
      <3>4. QED BY <3>1, <3>2, <3>3
    <2>2. CASE m \in msgs
      <3>1. m \in Messages BY <2>2 DEF TypeOK
      <3>2. /\ (m.type = "1b") =>
                /\ m.bal =< maxBal[m.acc]
                /\ \/ m.maxVBal = -1
                   \/ /\ m.maxVBal \in 0..(m.bal - 1)
                      /\ m.maxVal \in Values
                      /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                     \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)
            /\ (m.type = "2a") =>
                /\ SafeAt(m.val, m.bal)
                /\ \A m2 \in msgs :
                     (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
            /\ (m.type = "2b") =>
                 \E m2 \in msgs : /\ m2.type = "2a"
                                  /\ m2.bal = m.bal
                                  /\ m2.val = m.val
        BY <2>2 DEF MsgInv
      <3>3. ASSUME m.type = "1b" PROVE
              /\ m.bal =< maxBal'[m.acc]
              /\ \/ m.maxVBal = -1
                 \/ /\ m.maxVBal \in 0..(m.bal - 1)
                    /\ m.maxVal \in Values
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                   \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)'
        <4>1. m \in [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                      maxVal : Values \cup {None}, acc : Acceptors]
          BY <3>1, <3>3 DEF Messages
        <4>2. m.acc \in Acceptors /\ m.bal \in Ballots /\
              m.maxVBal \in Ballots \cup {-1} /\ m.maxVal \in Values \cup {None}
          BY <4>1
        <4>3. /\ m.bal =< maxBal[m.acc]
              /\ \/ m.maxVBal = -1
                 \/ /\ m.maxVBal \in 0..(m.bal - 1)
                    /\ m.maxVal \in Values
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
              /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                   \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)
          BY <3>2, <3>3
        <4>4. m.bal =< maxBal'[m.acc] BY <4>3, <1>3
        <4>5. \/ m.maxVBal = -1
              \/ /\ m.maxVBal \in 0..(m.bal - 1)
                 /\ m.maxVal \in Values
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
          <5>1. CASE m.maxVBal = -1 BY <5>1
          <5>2. CASE m.maxVBal \in 0..(m.bal - 1) /\ m.maxVal \in Values
                       /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            <6>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' BY <5>2, <1>5
            <6>2. QED BY <5>2, <6>1
          <5>3. QED BY <4>3, <5>1, <5>2
        <4>6. \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)'
          <5>1. SUFFICES ASSUME NEW b1 \in (m.maxVBal + 1)..(m.bal - 1),
                                 NEW v0 \in Values
                         PROVE ~ VotedForIn(m.acc, v0, b1)'
            OBVIOUS
          <5>2. ~ VotedForIn(m.acc, v0, b1) BY <5>1, <4>3
          <5>3. QED BY <5>2, <1>5
        <4>7. QED BY <4>4, <4>5, <4>6
      <3>4. ASSUME m.type = "2a" PROVE
              /\ SafeAt(m.val, m.bal)'
              /\ \A m2 \in msgs' :
                   (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
        <4>1. m \in [type : {"2a"}, bal : Ballots, val : Values]
          BY <3>1, <3>4 DEF Messages
        <4>2. SafeAt(m.val, m.bal) /\
              (\A m2 \in msgs :
                 (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val))
          BY <3>2, <3>4
        <4>3. SafeAt(m.val, m.bal)' BY <4>2, <1>7
        <4>4. \A m2 \in msgs' :
                (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
          <5>1. SUFFICES ASSUME NEW m2 \in msgs', m2.type = "2a", m2.bal = m.bal
                         PROVE m2.val = m.val
            OBVIOUS
          <5>2. CASE m2 = newm
            <6>1. m.bal = bb BY <5>2, <5>1 DEF newm
            <6>2. m \in msgs /\ m.type = "2a" /\ m.bal = bb
              BY <2>2, <3>4, <6>1
            <6>3. FALSE BY <6>2, <1>8
            <6>4. QED BY <6>3
          <5>3. CASE m2 \in msgs
            BY <5>3, <5>1, <4>2
          <5>4. QED BY <5>2, <5>3, <1>1
        <4>5. QED BY <4>3, <4>4
      <3>5. ASSUME m.type = "2b" PROVE
              \E m2 \in msgs' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
        <4>1. \E m2 \in msgs : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
          BY <3>2, <3>5
        <4>2. QED BY <4>1, <1>1
      <3>6. QED BY <3>3, <3>4, <3>5
    <2>3. QED BY <2>1, <2>2, <1>1
  <1>12. AccInv'
    <2> SUFFICES ASSUME NEW a \in Acceptors PROVE
          /\ maxBal'[a] >= maxVBal'[a]
          /\ (maxVBal'[a] # -1) =>
                /\ maxVBal'[a] \in Nat
                /\ maxVal'[a] \in Values
                /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                       /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          /\ \A v0 \in Values, b \in Ballots :
                VotedForIn(a, v0, b)' => maxVBal'[a] >= b
      BY DEF AccInv
    <2>1. maxBal'[a] = maxBal[a] /\ maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
      BY <1>3
    <2>2. /\ maxBal[a] >= maxVBal[a]
          /\ ((maxVBal[a] # -1) =>
                /\ maxVBal[a] \in Nat
                /\ maxVal[a] \in Values
                /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                       /\ mm.bal = maxVBal[a] /\ mm.acc = a)
          /\ (\A v0 \in Values, b \in Ballots :
                VotedForIn(a, v0, b) => maxVBal[a] >= b)
      BY DEF AccInv
    <2>3. maxBal'[a] >= maxVBal'[a] BY <2>1, <2>2
    <2>4. (maxVBal'[a] # -1) =>
            /\ maxVBal'[a] \in Nat
            /\ maxVal'[a] \in Values
            /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                   /\ mm.bal = maxVBal'[a] /\ mm.acc = a
      <3>1. ASSUME maxVBal'[a] # -1 PROVE
              /\ maxVBal'[a] \in Nat
              /\ maxVal'[a] \in Values
              /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                     /\ mm.bal = maxVBal'[a] /\ mm.acc = a
        <4>1. maxVBal[a] # -1 BY <3>1, <2>1
        <4>2. /\ maxVBal[a] \in Nat
              /\ maxVal[a] \in Values
              /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                     /\ mm.bal = maxVBal[a] /\ mm.acc = a
          BY <4>1, <2>2
        <4>3. \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                  /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          BY <4>2, <2>1, <1>1
        <4>4. QED BY <4>2, <4>3, <2>1
      <3>2. QED BY <3>1
    <2>5. \A v0 \in Values, b \in Ballots :
            VotedForIn(a, v0, b)' => maxVBal'[a] >= b
      <3>1. SUFFICES ASSUME NEW v0 \in Values, NEW b \in Ballots, VotedForIn(a, v0, b)'
                     PROVE maxVBal'[a] >= b
        OBVIOUS
      <3>2. VotedForIn(a, v0, b) BY <3>1, <1>5
      <3>3. maxVBal[a] >= b BY <3>2, <2>2
      <3>4. QED BY <3>3, <2>1
    <2>6. QED BY <2>3, <2>4, <2>5
  <1>13. QED BY <1>10, <1>11, <1>12 DEF IndInv

LEMMA L_Phase2b ==
  ASSUME IndInv, NEW ax \in Acceptors, Phase2b(ax)
  PROVE IndInv'
PROOF
  <1> USE QuorumAssumption DEF IndInv, TypeOK, AccInv, MsgInv
  <1>0. PICK m_2a \in msgs :
          /\ m_2a.type = "2a"
          /\ m_2a.bal >= maxBal[ax]
          /\ maxVBal' = [maxVBal EXCEPT ![ax] = m_2a.bal]
          /\ maxBal' = [maxBal EXCEPT ![ax] = m_2a.bal]
          /\ maxVal' = [maxVal EXCEPT ![ax] = m_2a.val]
          /\ msgs' = msgs \cup {[type |-> "2b", bal |-> m_2a.bal,
                                  val |-> m_2a.val, acc |-> ax]}
    BY DEF Phase2b, Send
  <1>. DEFINE newm == [type |-> "2b", bal |-> m_2a.bal, val |-> m_2a.val, acc |-> ax]
  <1>1. msgs' = msgs \cup {newm}
    BY <1>0 DEF newm
  <1>2. m_2a.bal \in Ballots /\ m_2a.val \in Values
    <2>1. m_2a \in Messages BY <1>0 DEF TypeOK
    <2>2. m_2a \in [type : {"2a"}, bal : Ballots, val : Values]
      BY <2>1, <1>0 DEF Messages
    <2>3. QED BY <2>2
  <1>3. m_2a.bal \in Nat BY <1>2 DEF Ballots
  <1>4. newm \in Messages BY <1>2 DEF newm, Messages
  <1>5. maxBal'[ax] = m_2a.bal /\ maxVBal'[ax] = m_2a.bal /\ maxVal'[ax] = m_2a.val
    BY <1>0, <1>2 DEF TypeOK
  <1>6. \A a \in Acceptors : a # ax =>
          maxBal'[a] = maxBal[a] /\ maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
    BY <1>0, <1>2 DEF TypeOK
  <1>7. /\ maxBal' \in [Acceptors -> Ballots \cup {-1}]
        /\ maxVBal' \in [Acceptors -> Ballots \cup {-1}]
        /\ maxVal' \in [Acceptors -> Values \cup {None}]
    BY <1>0, <1>2 DEF TypeOK
  <1>8. m_2a.bal >= maxBal[ax] BY <1>0
  <1>9. \A aa, vv, cc : VotedForIn(aa, vv, cc) => VotedForIn(aa, vv, cc)'
    BY <1>1 DEF VotedForIn
  <1>10. \A aa, vv, cc :
            VotedForIn(aa, vv, cc)' <=>
              (VotedForIn(aa, vv, cc) \/ (aa = ax /\ vv = m_2a.val /\ cc = m_2a.bal))
    <2>1. SUFFICES ASSUME NEW aa, NEW vv, NEW cc
                   PROVE VotedForIn(aa, vv, cc)' <=>
                          (VotedForIn(aa, vv, cc) \/
                           (aa = ax /\ vv = m_2a.val /\ cc = m_2a.bal))
      OBVIOUS
    <2>2. ASSUME VotedForIn(aa, vv, cc)'
          PROVE VotedForIn(aa, vv, cc) \/
                 (aa = ax /\ vv = m_2a.val /\ cc = m_2a.bal)
      <3>1. PICK mm \in msgs' :
              mm.type = "2b" /\ mm.val = vv /\ mm.bal = cc /\ mm.acc = aa
        BY <2>2 DEF VotedForIn
      <3>2. CASE mm = newm
        BY <3>2, <3>1 DEF newm
      <3>3. CASE mm \in msgs
        BY <3>3, <3>1 DEF VotedForIn
      <3>4. QED BY <3>2, <3>3, <1>1
    <2>3. ASSUME VotedForIn(aa, vv, cc) \/
                  (aa = ax /\ vv = m_2a.val /\ cc = m_2a.bal)
          PROVE VotedForIn(aa, vv, cc)'
      <3>1. CASE VotedForIn(aa, vv, cc) BY <3>1, <1>9
      <3>2. CASE aa = ax /\ vv = m_2a.val /\ cc = m_2a.bal
        <4>1. newm \in msgs' BY <1>1
        <4>2. newm.type = "2b" /\ newm.val = vv /\ newm.bal = cc /\ newm.acc = aa
          BY <3>2 DEF newm
        <4>3. QED BY <4>1, <4>2 DEF VotedForIn
      <3>3. QED BY <2>3, <3>1, <3>2
    <2>4. QED BY <2>2, <2>3
  <1>11. \A a \in Acceptors, c \in Nat :
            WontVoteIn(a, c) /\ (c # m_2a.bal \/ a # ax) => WontVoteIn(a, c)'
    <2>1. SUFFICES ASSUME NEW a \in Acceptors, NEW c \in Nat,
                          WontVoteIn(a, c), c # m_2a.bal \/ a # ax
                   PROVE WontVoteIn(a, c)'
      OBVIOUS
    <2>2. (\A v0 \in Values : ~ VotedForIn(a, v0, c)) /\ maxBal[a] > c
      BY <2>1 DEF WontVoteIn
    <2>3. \A v0 \in Values : ~ VotedForIn(a, v0, c)'
      <3>1. SUFFICES ASSUME NEW v0 \in Values PROVE ~ VotedForIn(a, v0, c)'
        OBVIOUS
      <3>2. ~ VotedForIn(a, v0, c) BY <2>2
      <3>3. ASSUME VotedForIn(a, v0, c)' PROVE FALSE
        <4>1. VotedForIn(a, v0, c) \/ (a = ax /\ v0 = m_2a.val /\ c = m_2a.bal)
          BY <3>3, <1>10
        <4>2. CASE VotedForIn(a, v0, c) BY <4>2, <3>2
        <4>3. CASE a = ax /\ v0 = m_2a.val /\ c = m_2a.bal
          BY <4>3, <2>1
        <4>4. QED BY <4>1, <4>2, <4>3
      <3>4. QED BY <3>3
    <2>4. maxBal'[a] > c
      <3>0. maxBal[a] \in Ballots \cup {-1} BY DEF TypeOK
      <3>0a. maxBal[a] > c BY <2>2
      <3>0b. maxBal[a] \in Nat BY <3>0a, <3>0 DEF Ballots
      <3>1. CASE a = ax
        <4>1. maxBal'[a] = m_2a.bal BY <3>1, <1>5
        <4>2. maxBal[a] > c BY <2>2
        <4>3. m_2a.bal >= maxBal[ax] BY <1>8
        <4>4. m_2a.bal > c BY <4>2, <4>3, <3>1, <3>0b, <1>3 DEF Ballots
        <4>5. QED BY <4>1, <4>4
      <3>2. CASE a # ax
        <4>1. maxBal'[a] = maxBal[a] BY <3>2, <1>6
        <4>2. QED BY <4>1, <2>2
      <3>3. QED BY <3>1, <3>2
    <2>5. QED BY <2>3, <2>4 DEF WontVoteIn
  <1>12. \A v0 \in Values, b \in Nat : SafeAt(v0, b) => SafeAt(v0, b)'
    <2>1. SUFFICES ASSUME NEW v0 \in Values, NEW b \in Nat, SafeAt(v0, b)
                   PROVE SafeAt(v0, b)'
      OBVIOUS
    <2>2. SUFFICES ASSUME NEW c \in 0..(b-1)
                   PROVE \E Q \in Quorums :
                          \A a \in Q : VotedForIn(a, v0, c)' \/ WontVoteIn(a, c)'
      BY DEF SafeAt
    <2>3. c \in Nat BY <2>2
    <2>4. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v0, c) \/ WontVoteIn(a, c)
      BY <2>1, <2>2 DEF SafeAt
    <2>5. \A a \in Q : VotedForIn(a, v0, c)' \/ WontVoteIn(a, c)'
      <3>1. SUFFICES ASSUME NEW a \in Q
                     PROVE VotedForIn(a, v0, c)' \/ WontVoteIn(a, c)'
        OBVIOUS
      <3>2. a \in Acceptors BY <3>1, QuorumAssumption
      <3>3. VotedForIn(a, v0, c) \/ WontVoteIn(a, c) BY <2>4, <3>1
      <3>4. CASE VotedForIn(a, v0, c) BY <3>4, <1>9
      <3>5. CASE WontVoteIn(a, c)
        <4>1. CASE c # m_2a.bal \/ a # ax
          BY <3>5, <4>1, <1>11, <3>2, <2>3
        <4>2. CASE c = m_2a.bal /\ a = ax
          <5>1. maxBal[ax] > c BY <3>5, <4>2 DEF WontVoteIn
          <5>2. maxBal[ax] > m_2a.bal BY <5>1, <4>2
          <5>3. m_2a.bal >= maxBal[ax] BY <1>8
          <5>3a. maxBal[ax] \in Ballots \cup {-1} BY DEF TypeOK
          <5>4. FALSE BY <5>2, <5>3, <5>3a, <1>3 DEF Ballots
          <5>5. QED BY <5>4
        <4>3. QED BY <4>1, <4>2
      <3>6. QED BY <3>3, <3>4, <3>5
    <2>6. QED BY <2>5
  <1>20. TypeOK'
    BY <1>1, <1>4, <1>7 DEF TypeOK
  <1>21. MsgInv'
    <2> SUFFICES ASSUME NEW m \in msgs'
                 PROVE
                   /\ (m.type = "1b") =>
                        /\ m.bal =< maxBal'[m.acc]
                        /\ \/ m.maxVBal = -1
                           \/ /\ m.maxVBal \in 0..(m.bal - 1)
                              /\ m.maxVal \in Values
                              /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                        /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                             \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)'
                   /\ (m.type = "2a") =>
                        /\ SafeAt(m.val, m.bal)'
                        /\ \A m2 \in msgs' :
                             (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
                   /\ (m.type = "2b") =>
                        \E m2 \in msgs' : /\ m2.type = "2a"
                                          /\ m2.bal = m.bal
                                          /\ m2.val = m.val
      BY DEF MsgInv
    <2>1. CASE m = newm
      <3>1. m.type = "2b" /\ m.bal = m_2a.bal /\ m.val = m_2a.val /\ m.acc = ax
        BY <2>1 DEF newm
      <3>2. \E m2 \in msgs' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
        <4>1. m_2a \in msgs' BY <1>1
        <4>2. m_2a.type = "2a" /\ m_2a.bal = m.bal /\ m_2a.val = m.val
          BY <1>0, <3>1
        <4>3. QED BY <4>1, <4>2
      <3>3. QED BY <3>1, <3>2
    <2>2. CASE m \in msgs
      <3>1. m \in Messages BY <2>2 DEF TypeOK
      <3>2. /\ (m.type = "1b") =>
                /\ m.bal =< maxBal[m.acc]
                /\ \/ m.maxVBal = -1
                   \/ /\ m.maxVBal \in 0..(m.bal - 1)
                      /\ m.maxVal \in Values
                      /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                     \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)
            /\ (m.type = "2a") =>
                /\ SafeAt(m.val, m.bal)
                /\ \A m2 \in msgs :
                     (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
            /\ (m.type = "2b") =>
                 \E m2 \in msgs : /\ m2.type = "2a"
                                  /\ m2.bal = m.bal
                                  /\ m2.val = m.val
        BY <2>2 DEF MsgInv
      <3>3. ASSUME m.type = "1b" PROVE
              /\ m.bal =< maxBal'[m.acc]
              /\ \/ m.maxVBal = -1
                 \/ /\ m.maxVBal \in 0..(m.bal - 1)
                    /\ m.maxVal \in Values
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
              /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                   \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)'
        <4>1. m \in [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                      maxVal : Values \cup {None}, acc : Acceptors]
          BY <3>1, <3>3 DEF Messages
        <4>2. m.acc \in Acceptors /\ m.bal \in Ballots /\
              m.maxVBal \in Ballots \cup {-1} /\ m.maxVal \in Values \cup {None}
          BY <4>1
        <4>3. /\ m.bal =< maxBal[m.acc]
              /\ \/ m.maxVBal = -1
                 \/ /\ m.maxVBal \in 0..(m.bal - 1)
                    /\ m.maxVal \in Values
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
              /\ \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                   \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)
          BY <3>2, <3>3
        <4>4. m.bal =< maxBal'[m.acc]
          <5>1. CASE m.acc = ax
            <6>1. maxBal'[m.acc] = m_2a.bal BY <5>1, <1>5
            <6>2. m.bal =< maxBal[ax] BY <4>3, <5>1
            <6>3. m_2a.bal >= maxBal[ax] BY <1>8
            <6>3a. maxBal[ax] \in Ballots \cup {-1} BY DEF TypeOK
            <6>3b. maxBal[ax] \in Nat
              <7>1. m.bal \in Nat BY <4>2 DEF Ballots
              <7>2. QED BY <6>2, <6>3a, <7>1 DEF Ballots
            <6>4. m.bal =< m_2a.bal BY <6>2, <6>3, <6>3b, <4>2, <1>3 DEF Ballots
            <6>5. QED BY <6>4, <6>1
          <5>2. CASE m.acc # ax
            <6>1. maxBal'[m.acc] = maxBal[m.acc] BY <5>2, <1>6, <4>2
            <6>2. QED BY <6>1, <4>3
          <5>3. QED BY <5>1, <5>2
        <4>5. \/ m.maxVBal = -1
              \/ /\ m.maxVBal \in 0..(m.bal - 1)
                 /\ m.maxVal \in Values
                 /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
          <5>1. CASE m.maxVBal = -1 BY <5>1
          <5>2. CASE m.maxVBal \in 0..(m.bal - 1) /\ m.maxVal \in Values
                       /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
            <6>1. VotedForIn(m.acc, m.maxVal, m.maxVBal)' BY <5>2, <1>9
            <6>2. QED BY <5>2, <6>1
          <5>3. QED BY <4>3, <5>1, <5>2
        <4>6. \A b1 \in (m.maxVBal + 1)..(m.bal - 1) :
                \A v0 \in Values : ~ VotedForIn(m.acc, v0, b1)'
          <5>1. SUFFICES ASSUME NEW b1 \in (m.maxVBal + 1)..(m.bal - 1),
                                 NEW v0 \in Values
                         PROVE ~ VotedForIn(m.acc, v0, b1)'
            OBVIOUS
          <5>2. b1 \in Nat
            <6>1. m.maxVBal + 1 \in Nat BY <4>2 DEF Ballots
            <6>2. QED BY <5>1, <6>1
          <5>3. ~ VotedForIn(m.acc, v0, b1) BY <5>1, <4>3
          <5>4. ASSUME VotedForIn(m.acc, v0, b1)' PROVE FALSE
            <6>1. VotedForIn(m.acc, v0, b1) \/
                    (m.acc = ax /\ v0 = m_2a.val /\ b1 = m_2a.bal)
              BY <5>4, <1>10
            <6>2. CASE VotedForIn(m.acc, v0, b1)
              BY <6>2, <5>3
            <6>3. CASE m.acc = ax /\ v0 = m_2a.val /\ b1 = m_2a.bal
              <7>1. b1 < m.bal BY <5>1, <4>2 DEF Ballots
              <7>2. m.bal =< maxBal[m.acc] BY <4>3
              <7>3. maxBal[m.acc] = maxBal[ax] BY <6>3
              <7>4. m_2a.bal >= maxBal[ax] BY <1>8
              <7>4a. maxBal[ax] \in Ballots \cup {-1} BY DEF TypeOK
              <7>4b. maxBal[ax] \in Nat
                <8>1. m.bal \in Nat BY <4>2 DEF Ballots
                <8>2. QED BY <7>2, <7>3, <7>4a, <8>1 DEF Ballots
              <7>5. m.bal =< m_2a.bal BY <7>2, <7>3, <7>4, <7>4b, <4>2, <1>3 DEF Ballots
              <7>6. b1 = m_2a.bal BY <6>3
              <7>6a. m.bal \in Nat BY <4>2 DEF Ballots
              <7>7. b1 < b1 BY <7>1, <7>5, <7>6, <5>2, <1>3, <7>6a DEF Ballots
              <7>8. QED BY <7>7
            <6>4. QED BY <6>1, <6>2, <6>3
          <5>5. QED BY <5>4
        <4>7. QED BY <4>4, <4>5, <4>6
      <3>4. ASSUME m.type = "2a" PROVE
              /\ SafeAt(m.val, m.bal)'
              /\ \A m2 \in msgs' :
                   (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
        <4>1. m \in [type : {"2a"}, bal : Ballots, val : Values]
          BY <3>1, <3>4 DEF Messages
        <4>2. m.val \in Values /\ m.bal \in Ballots BY <4>1
        <4>3. m.bal \in Nat BY <4>2 DEF Ballots
        <4>4. SafeAt(m.val, m.bal) /\
              (\A m2 \in msgs :
                 (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val))
          BY <3>2, <3>4
        <4>5. SafeAt(m.val, m.bal)' BY <4>4, <1>12, <4>2, <4>3
        <4>6. \A m2 \in msgs' :
                (m2.type = "2a") /\ (m2.bal = m.bal) => (m2.val = m.val)
          <5>1. SUFFICES ASSUME NEW m2 \in msgs', m2.type = "2a", m2.bal = m.bal
                         PROVE m2.val = m.val
            OBVIOUS
          <5>2. m2 # newm BY <5>1 DEF newm
          <5>3. m2 \in msgs BY <5>1, <5>2, <1>1
          <5>4. QED BY <5>3, <5>1, <4>4
        <4>7. QED BY <4>5, <4>6
      <3>5. ASSUME m.type = "2b" PROVE
              \E m2 \in msgs' : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
        <4>1. \E m2 \in msgs : m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val
          BY <3>2, <3>5
        <4>2. QED BY <4>1, <1>1
      <3>6. QED BY <3>3, <3>4, <3>5
    <2>3. QED BY <2>1, <2>2, <1>1
  <1>22. AccInv'
    <2> SUFFICES ASSUME NEW a \in Acceptors PROVE
          /\ maxBal'[a] >= maxVBal'[a]
          /\ (maxVBal'[a] # -1) =>
                /\ maxVBal'[a] \in Nat
                /\ maxVal'[a] \in Values
                /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                       /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          /\ \A v0 \in Values, b \in Ballots :
                VotedForIn(a, v0, b)' => maxVBal'[a] >= b
      BY DEF AccInv
    <2>1. /\ maxBal[a] >= maxVBal[a]
          /\ ((maxVBal[a] # -1) =>
                /\ maxVBal[a] \in Nat
                /\ maxVal[a] \in Values
                /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                       /\ mm.bal = maxVBal[a] /\ mm.acc = a)
          /\ (\A v0 \in Values, b \in Ballots :
                VotedForIn(a, v0, b) => maxVBal[a] >= b)
      BY DEF AccInv
    <2>2. CASE a = ax
      <3>1. maxBal'[a] = m_2a.bal /\ maxVBal'[a] = m_2a.bal /\ maxVal'[a] = m_2a.val
        BY <2>2, <1>5
      <3>2. maxBal'[a] >= maxVBal'[a] BY <3>1, <1>3 DEF Ballots
      <3>3. (maxVBal'[a] # -1) =>
              /\ maxVBal'[a] \in Nat
              /\ maxVal'[a] \in Values
              /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                     /\ mm.bal = maxVBal'[a] /\ mm.acc = a
        <4>1. maxVBal'[a] \in Nat /\ maxVal'[a] \in Values BY <3>1, <1>2, <1>3
        <4>2. \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                   /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          <5>1. a = ax /\ maxVal'[a] = m_2a.val /\ maxVBal'[a] = m_2a.bal
            BY <2>2, <3>1
          <5>2. newm \in msgs'
            BY <1>1
          <5>3. newm.type = "2b" /\ newm.val = m_2a.val /\ newm.bal = m_2a.bal
                  /\ newm.acc = ax
            BY DEF newm
          <5>4. QED BY <5>1, <5>2, <5>3
        <4>3. QED BY <4>1, <4>2
      <3>4. \A v0 \in Values, b \in Ballots :
              VotedForIn(a, v0, b)' => maxVBal'[a] >= b
        <4>1. SUFFICES ASSUME NEW v0 \in Values, NEW b \in Ballots,
                              VotedForIn(a, v0, b)'
                       PROVE maxVBal'[a] >= b
          OBVIOUS
        <4>2. b \in Nat BY DEF Ballots
        <4>3. VotedForIn(a, v0, b) \/
                (a = ax /\ v0 = m_2a.val /\ b = m_2a.bal)
          BY <4>1, <1>10
        <4>4. CASE VotedForIn(a, v0, b)
          <5>1. maxVBal[a] >= b BY <4>4, <2>1
          <5>2. maxBal[a] >= maxVBal[a] BY <2>1
          <5>3. m_2a.bal >= maxBal[ax] BY <1>8
          <5>3a. /\ maxBal[a] \in Ballots \cup {-1}
                 /\ maxVBal[a] \in Ballots \cup {-1}
            BY DEF TypeOK
          <5>3b. maxVBal[a] \in Nat BY <5>1, <5>3a, <4>2 DEF Ballots
          <5>3c. maxBal[a] \in Nat BY <5>2, <5>3a, <5>3b DEF Ballots
          <5>4. m_2a.bal >= b
            BY <5>1, <5>2, <5>3, <2>2, <5>3b, <5>3c, <4>2, <1>3 DEF Ballots
          <5>5. QED BY <5>4, <3>1
        <4>5. CASE a = ax /\ v0 = m_2a.val /\ b = m_2a.bal
          BY <4>5, <3>1, <1>3 DEF Ballots
        <4>6. QED BY <4>3, <4>4, <4>5
      <3>5. QED BY <3>2, <3>3, <3>4
    <2>3. CASE a # ax
      <3>1. maxBal'[a] = maxBal[a] /\ maxVBal'[a] = maxVBal[a] /\ maxVal'[a] = maxVal[a]
        BY <2>3, <1>6
      <3>2. maxBal'[a] >= maxVBal'[a] BY <3>1, <2>1
      <3>3. (maxVBal'[a] # -1) =>
              /\ maxVBal'[a] \in Nat
              /\ maxVal'[a] \in Values
              /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                     /\ mm.bal = maxVBal'[a] /\ mm.acc = a
        <4>1. ASSUME maxVBal'[a] # -1 PROVE
                /\ maxVBal'[a] \in Nat
                /\ maxVal'[a] \in Values
                /\ \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                       /\ mm.bal = maxVBal'[a] /\ mm.acc = a
          <5>1. maxVBal[a] # -1 BY <4>1, <3>1
          <5>2. /\ maxVBal[a] \in Nat
                /\ maxVal[a] \in Values
                /\ \E mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[a]
                                       /\ mm.bal = maxVBal[a] /\ mm.acc = a
            BY <5>1, <2>1
          <5>3. \E mm \in msgs' : mm.type = "2b" /\ mm.val = maxVal'[a]
                                    /\ mm.bal = maxVBal'[a] /\ mm.acc = a
            BY <5>2, <3>1, <1>1
          <5>4. QED BY <5>2, <5>3, <3>1
        <4>2. QED BY <4>1
      <3>4. \A v0 \in Values, b \in Ballots :
              VotedForIn(a, v0, b)' => maxVBal'[a] >= b
        <4>1. SUFFICES ASSUME NEW v0 \in Values, NEW b \in Ballots,
                              VotedForIn(a, v0, b)'
                       PROVE maxVBal'[a] >= b
          OBVIOUS
        <4>2. b \in Nat BY DEF Ballots
        <4>3. VotedForIn(a, v0, b) \/
                (a = ax /\ v0 = m_2a.val /\ b = m_2a.bal)
          BY <4>1, <1>10
        <4>4. ~ (a = ax) BY <2>3
        <4>5. VotedForIn(a, v0, b) BY <4>3, <4>4
        <4>6. maxVBal[a] >= b BY <4>5, <2>1
        <4>7. QED BY <4>6, <3>1
      <3>5. QED BY <3>2, <3>3, <3>4
    <2>4. QED BY <2>2, <2>3
  <1>23. QED BY <1>20, <1>21, <1>22 DEF IndInv

LEMMA L_Stutter ==
  ASSUME IndInv, UNCHANGED vars
  PROVE IndInv'
PROOF
  <1>1. msgs' = msgs /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
    BY DEF vars
  <1>2. \A aa, vv, cc : VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
    BY <1>1 DEF VotedForIn
  <1>3. \A aa, cc : WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
    BY <1>1, <1>2 DEF WontVoteIn
  <1>4. \A vv, bx : SafeAt(vv, bx)' <=> SafeAt(vv, bx)
    BY <1>2, <1>3 DEF SafeAt
  <1>5. TypeOK' BY <1>1 DEF IndInv, TypeOK
  <1>6. MsgInv' BY <1>1, <1>2, <1>4 DEF IndInv, MsgInv
  <1>7. AccInv' BY <1>1, <1>2 DEF IndInv, AccInv
  <1>8. QED BY <1>5, <1>6, <1>7 DEF IndInv

LEMMA L_Next == IndInv /\ [Next]_vars => IndInv'
PROOF
  <1> SUFFICES ASSUME IndInv, [Next]_vars PROVE IndInv'
    OBVIOUS
  <1>1. CASE Next
    <2>1. CASE \E b \in Ballots : Phase1a(b)
      <3>1. PICK b \in Ballots : Phase1a(b) BY <2>1
      <3>2. QED BY <3>1, L_Phase1a
    <2>2. CASE \E b \in Ballots : Phase2a(b)
      <3>1. PICK b \in Ballots : Phase2a(b) BY <2>2
      <3>2. QED BY <3>1, L_Phase2a
    <2>3. CASE \E a \in Acceptors : Phase1b(a)
      <3>1. PICK a \in Acceptors : Phase1b(a) BY <2>3
      <3>2. QED BY <3>1, L_Phase1b
    <2>4. CASE \E a \in Acceptors : Phase2b(a)
      <3>1. PICK a \in Acceptors : Phase2b(a) BY <2>4
      <3>2. QED BY <3>1, L_Phase2b
    <2>5. QED BY <2>1, <2>2, <2>3, <2>4, <1>1 DEF Next
  <1>2. CASE UNCHANGED vars
    BY <1>2, L_Stutter
  <1>3. QED BY <1>1, <1>2

-----------------------------------------------------------------------------

THEOREM Consistent == Spec => []Consistency
PROOF
  <1>1. Spec => []IndInv
    <2>1. Init => IndInv BY L_Init
    <2>2. IndInv /\ [Next]_vars => IndInv' BY L_Next
    <2>3. QED BY <2>1, <2>2, PTL DEF Spec
  <1>2. IndInv => Consistency BY Cons_Lemma
  <1>3. QED BY <1>1, <1>2, PTL

-----------------------------------------------------------------------------

=============================================================================
