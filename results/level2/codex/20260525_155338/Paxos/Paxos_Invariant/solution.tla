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

MsgOK(m) ==
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

AccOK(a) ==
    /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
    /\ maxVBal[a] =< maxBal[a]
    /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
    /\ \A c \in Ballots : c > maxVBal[a] => ~ \E v \in Values : VotedForIn(a, v, c)

THEOREM MsgInvOK == MsgInv <=> \A m \in msgs : MsgOK(m)
PROOF
  BY DEF MsgInv, MsgOK

THEOREM AccInvOK == AccInv <=> \A a \in Acceptors : AccOK(a)
PROOF
  BY DEF AccInv, AccOK

-----------------------------------------------------------------------------
Inv == TypeOK /\ MsgInv /\ AccInv
-----------------------------------------------------------------------------

THEOREM VoteUnique ==
  ASSUME Inv,
         NEW a \in Acceptors,
         NEW b \in Ballots,
         NEW v1 \in Values,
         NEW v2 \in Values,
         VotedForIn(a, v1, b),
         VotedForIn(a, v2, b)
  PROVE  v1 = v2
PROOF
  BY SMTT(20) DEF Inv, TypeOK, MsgInv, VotedForIn, SafeAt, WontVoteIn, Ballots

THEOREM VoteSafe ==
  ASSUME Inv,
         NEW a \in Acceptors,
         NEW b \in Ballots,
         NEW v \in Values,
         VotedForIn(a, v, b)
  PROVE  SafeAt(v, b)
PROOF
  BY SMTT(20) DEF Inv, TypeOK, MsgInv, VotedForIn, SafeAt, WontVoteIn, Ballots

THEOREM OneBMaxBal ==
  ASSUME Inv,
         NEW r \in msgs,
         r.type = "1b"
  PROVE  r.bal =< maxBal[r.acc]
PROOF
  BY SMTT(10) DEF Inv, MsgInv

THEOREM OneBNoVoteAfter ==
  ASSUME Inv,
         NEW r \in msgs,
         r.type = "1b",
         NEW c \in (r.maxVBal+1)..(r.bal-1)
  PROVE  WontVoteIn(r.acc, c)
PROOF
<1>1. \A v \in Values : ~ VotedForIn(r.acc, v, c)
  BY SMTT(10) DEF Inv, MsgInv, VotedForIn, Ballots
<1>2. r.bal =< maxBal[r.acc]
  BY OneBMaxBal
<1>3. maxBal[r.acc] > c
  BY <1>2, SMTT(10) DEF Inv, TypeOK, MsgInv, Messages, Ballots
<1>4. QED
  BY <1>1, <1>3 DEF WontVoteIn

THEOREM OneBVoteAtMax ==
  ASSUME Inv,
         NEW r \in msgs,
         r.type = "1b",
         r.maxVBal \in Ballots
  PROVE  /\ r.maxVal \in Values
         /\ VotedForIn(r.acc, r.maxVal, r.maxVBal)
PROOF
  BY SMTT(20) DEF Inv, TypeOK, MsgInv, VotedForIn, Ballots

-----------------------------------------------------------------------------

THEOREM InitInv == Init => Inv
PROOF
  BY DEF Init, Inv, TypeOK, MsgInv, AccInv, VotedForIn, Messages, Ballots, None

THEOREM StutterInv == Inv /\ UNCHANGED vars => Inv'
PROOF
  BY SMT DEF Inv, TypeOK, MsgInv, AccInv, vars, VotedForIn, WontVoteIn, SafeAt

THEOREM Phase1aInv == Inv /\ (\E b \in Ballots : Phase1a(b)) => Inv'
PROOF
  BY SMTT(20) DEF Inv, TypeOK, MsgInv, AccInv, Phase1a, Send,
                  VotedForIn, WontVoteIn, SafeAt, Messages, Ballots

THEOREM Phase1bInv == Inv /\ (\E a \in Acceptors : Phase1b(a)) => Inv'
PROOF
<1>1. ASSUME Inv, \E a \in Acceptors : Phase1b(a)
      PROVE  Inv'
  <2>1. TypeOK'
    BY <1>1, SMTT(10) DEF Inv, TypeOK, Phase1b, Send, Messages, Ballots
  <2>2. \A m \in msgs' : MsgOK(m)'
    <3>1. ASSUME NEW m \in msgs'
          PROVE  MsgOK(m)'
      <4>1. CASE m \in msgs
        <5>1. MsgOK(m)
          BY <1>1, <4>1, MsgInvOK DEF Inv
        <5>2. CASE m.type = "1b"
          BY <1>1, <4>1, <5>1, <5>2, SMTT(10)
             DEF Inv, TypeOK, MsgOK, Phase1b, Send, VotedForIn, WontVoteIn,
                 SafeAt, Messages, Ballots
        <5>3. CASE m.type = "2a"
          <6>1. SafeAt(m.val, m.bal)
            BY <5>1, <5>3 DEF MsgOK
          <6>2. SafeAt(m.val, m.bal)'
            <7>1. ASSUME NEW c \in 0..(m.bal-1)
                  PROVE  \E Q \in Quorums :
                           \A aa \in Q :
                             VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
              <8>1. PICK Q \in Quorums :
                      \A aa \in Q : VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
                BY <6>1, <7>1 DEF SafeAt
              <8>2. \A aa \in Q :
                       VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
                <9>1. ASSUME NEW aa \in Q
                      PROVE  VotedForIn(aa, m.val, c)' \/ WontVoteIn(aa, c)'
                  <10>1. VotedForIn(aa, m.val, c) \/ WontVoteIn(aa, c)
                    BY <8>1, <9>1
                  <10>2. CASE VotedForIn(aa, m.val, c)
                    BY <1>1, <10>2, SMTT(10) DEF Phase1b, Send, VotedForIn
                  <10>3. CASE WontVoteIn(aa, c)
                    <11>1. \A v \in Values : ~ VotedForIn(aa, v, c)'
                      BY <1>1, <10>3, SMTT(10)
                         DEF Phase1b, Send, VotedForIn, WontVoteIn
                    <11>2. maxBal'[aa] > c
                      <12>1. PICK ab \in Acceptors : Phase1b(ab)
                        BY <1>1
                      <12>2. PICK mb \in msgs :
                                /\ mb.type = "1a"
                                /\ mb.bal > maxBal[ab]
                                /\ maxBal' = [maxBal EXCEPT ![ab] = mb.bal]
                        BY <12>1 DEF Phase1b
                      <12>3. CASE aa = ab
                        <13>1. maxBal'[aa] = mb.bal
                          BY <12>2, <12>3
                        <13>2. mb.bal > maxBal[aa]
                          BY <12>2, <12>3
                        <13>3. maxBal[aa] > c
                          BY <10>3 DEF WontVoteIn
                        <13>4. aa \in Acceptors
                          BY <8>1, <9>1, QuorumAssumption
                        <13>5. /\ mb.bal \in Int
                                /\ maxBal[aa] \in Int
                                /\ c \in Int
                          BY <1>1, <7>1, <12>2, <13>4, SMTT(5)
                             DEF Inv, TypeOK, Messages, Ballots
                        <13>6. mb.bal > c
                          BY <13>2, <13>3, <13>5, SimpleArithmetic
                        <13>7. QED
                          BY <13>1, <13>6
                      <12>4. CASE aa # ab
                        <13>1. maxBal'[aa] = maxBal[aa]
                          BY <12>2, <12>4
                        <13>2. maxBal[aa] > c
                          BY <10>3 DEF WontVoteIn
                        <13>3. QED
                          BY <13>1, <13>2
                      <12>5. QED
                        BY <12>3, <12>4
                    <11>3. QED
                      BY <11>1, <11>2 DEF WontVoteIn
                  <10>4. QED
                    BY <10>1, <10>2, <10>3
                <9>2. QED
                  BY <9>1
              <8>3. QED
                BY <8>1, <8>2
            <7>2. QED
              BY <7>1 DEF SafeAt
          <6>3. \A ma \in msgs' :
                   (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
            BY <1>1, <5>1, <5>3, SMTT(10)
               DEF Phase1b, Send, MsgOK
          <6>4. QED
            BY <5>3, <6>2, <6>3 DEF MsgOK
        <5>4. CASE m.type = "2b"
          BY <1>1, <4>1, <5>1, <5>4, SMTT(10)
             DEF Inv, TypeOK, MsgOK, Phase1b, Send, VotedForIn, WontVoteIn,
                 SafeAt, Messages, Ballots
        <5>5. CASE m.type = "1a"
          BY <1>1, <4>1, <5>1, <5>5, SMTT(10)
             DEF Inv, TypeOK, MsgOK, Phase1b, Send, VotedForIn, WontVoteIn,
                 SafeAt, Messages, Ballots
        <5>6. QED
          BY <1>1, <4>1, <5>2, <5>3, <5>4, <5>5
             DEF Inv, TypeOK, Messages
      <4>2. CASE m \notin msgs
        BY <1>1, <3>1, <4>2, SMTT(10) DEF Inv, TypeOK, MsgInv, AccInv, MsgOK,
                                                Phase1b, Send, VotedForIn,
                                                WontVoteIn, SafeAt, Messages,
                                                Ballots
      <4>3. QED
        BY <4>1, <4>2
    <3>2. QED
      BY <3>1
  <2>3. MsgInv'
    BY <2>2 DEF MsgInv, MsgOK
  <2>4. AccInv'
    BY <1>1, SMTT(10) DEF Inv, TypeOK, MsgInv, AccInv, Phase1b, Send,
                            VotedForIn, WontVoteIn, SafeAt, Messages, Ballots
  <2>5. QED
    BY <2>1, <2>3, <2>4 DEF Inv
<1>2. QED
  BY <1>1

THEOREM Phase2aInv == Inv /\ (\E b \in Ballots : Phase2a(b)) => Inv'
PROOF
<1>1. ASSUME Inv, \E b \in Ballots : Phase2a(b)
      PROVE  Inv'
  <2>1. TypeOK'
    BY <1>1, SMTT(10) DEF Inv, TypeOK, Phase2a, Send, Messages, Ballots
  <2>2. \A m \in msgs' : MsgOK(m)'
    <3>1. ASSUME NEW m \in msgs'
          PROVE  MsgOK(m)'
      <4>1. CASE m \in msgs
        BY <1>1, <4>1, MsgInvOK, SMTT(20)
           DEF Inv, TypeOK, MsgInv, AccInv, MsgOK, Phase2a, Send,
               VotedForIn, WontVoteIn, SafeAt, Messages, Ballots
      <4>2. CASE m \notin msgs
        BY <1>1, <3>1, <4>2, VoteUnique, VoteSafe, SMTT(30)
           DEF Inv, TypeOK, MsgInv, AccInv, MsgOK, Phase2a, Send,
               VotedForIn, WontVoteIn, SafeAt, Messages, Ballots
      <4>3. QED
        BY <4>1, <4>2
    <3>2. QED
      BY <3>1
  <2>3. MsgInv'
    BY <2>2 DEF MsgInv, MsgOK
  <2>4. AccInv'
    BY <1>1, SMTT(10) DEF Inv, TypeOK, MsgInv, AccInv, Phase2a, Send,
                            VotedForIn, WontVoteIn, SafeAt, Messages, Ballots
  <2>5. QED
    BY <2>1, <2>3, <2>4 DEF Inv
<1>2. QED
  BY <1>1

THEOREM Phase2bInv == Inv /\ (\E a \in Acceptors : Phase2b(a)) => Inv'
PROOF
<1>1. ASSUME Inv, \E a \in Acceptors : Phase2b(a)
      PROVE  Inv'
  <2>1. TypeOK'
    BY <1>1, SMTT(10) DEF Inv, TypeOK, MsgInv, Phase2b, Send,
                            Messages, Ballots
  <2>2. MsgInv'
    BY <1>1, SMTT(20) DEF Inv, TypeOK, MsgInv, AccInv, Phase2b, Send,
                            VotedForIn, WontVoteIn, SafeAt, Messages, Ballots
  <2>3. AccInv'
    BY <1>1, SMTT(10) DEF Inv, TypeOK, MsgInv, AccInv, Phase2b, Send,
                            VotedForIn, WontVoteIn, SafeAt, Messages, Ballots
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Inv
<1>2. QED
  BY <1>1

THEOREM NextInv == Inv /\ [Next]_vars => Inv'
PROOF
  BY StutterInv, Phase1aInv, Phase1bInv, Phase2aInv, Phase2bInv
     DEF Next, vars

THEOREM Invariant == Spec => []Inv
PROOF
  BY InitInv, NextInv, PTL DEF Spec

-----------------------------------------------------------------------------

=============================================================================
