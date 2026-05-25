------------------------------- MODULE Paxos_Refinement -------------------------------
(* 
Specification and Verification of Basic Paxos.

See http://research.microsoft.com/en-us/um/people/lamport/pubs/pubs.html#paxos-simple
*)
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
VARIABLES msgs,    \* the set of messages that have been sent.
          maxBal,  \* maxBal[a]: the highest-number ballot acceptor a has participated in.
          maxVBal, \* maxVBal[a]: the highest ballot in which a has voted;
          maxVal   \* maxVal[a]: the value it voted for in that ballot.

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

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
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
                                \* conjunct strengthened 2014/04/02 sm
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
                                \* /\ SafeAt(m.maxVal, m.maxVBal)
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
                          \* conjunct added 2014/03/29 sm
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
    \* conjunct strengthened corresponding to MsgInv 2014/04/02 sm
    /\ (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])  \* SafeAt(maxVal[a], maxVBal[a])
    \* conjunct added corresponding to MsgInv 2014/03/29 sm
    /\ \A c \in Ballots : c > maxVBal[a] => ~ \E v \in Values : VotedForIn(a, v, c)
-----------------------------------------------------------------------------
Inv == TypeOK /\ MsgInv /\ AccInv
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b) is stable, meaning that once it becomes true, it *)
(* remains true throughout the rest of the excecution.                     *)
(***************************************************************************)


    

-----------------------------------------------------------------------------
chosenBar == {v \in Values : Chosen(v)}

C == INSTANCE Consensus WITH chosen <- chosenBar
-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper lemmas and the inductive invariant for the refinement proof.     *)
(***************************************************************************)
USE DEF Ballots

LEMMA NoneNotInValues == None \notin Values
  BY NoSetContainsEverything DEF None

(* msgs only grows in any step. *)
LEMMA MsgsSubset ==
  ASSUME [Next]_vars
  PROVE  msgs \subseteq msgs'
<1>1. CASE Next
  BY <1>1 DEF Next, Phase1a, Phase1b, Phase2a, Phase2b, Send
<1>2. CASE vars' = vars
  BY <1>2 DEF vars
<1> QED
  BY <1>1, <1>2

(* VotedForIn is stable: once true, stays true. *)
LEMMA VotedForInStable ==
  ASSUME [Next]_vars, NEW a, NEW v, NEW b, VotedForIn(a, v, b)
  PROVE  VotedForIn(a, v, b)'
<1>1. msgs \subseteq msgs'
  BY MsgsSubset
<1> QED
  BY <1>1 DEF VotedForIn

(* A 2b vote for v at b implies v was safe at b. *)
LEMMA VotedInv ==
  MsgInv /\ TypeOK =>
    \A a \in Acceptors, v \in Values, b \in Ballots :
      VotedForIn(a, v, b) => SafeAt(v, b)
<1> SUFFICES ASSUME MsgInv, TypeOK,
                    NEW a \in Acceptors, NEW v \in Values, NEW b \in Ballots,
                    VotedForIn(a, v, b)
             PROVE  SafeAt(v, b)
  OBVIOUS
<1>1. PICK m \in msgs : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a
  BY DEF VotedForIn
<1>2. PICK ma \in msgs : ma.type = "2a" /\ ma.bal = b /\ ma.val = v
  BY <1>1 DEF MsgInv
<1> QED
  BY <1>2 DEF MsgInv

(* At most one value is voted for in a given ballot. *)
LEMMA VotedOnce ==
  MsgInv => \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
              VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
<1> SUFFICES ASSUME MsgInv,
                    NEW a1 \in Acceptors, NEW a2 \in Acceptors, NEW b \in Ballots,
                    NEW v1 \in Values, NEW v2 \in Values,
                    VotedForIn(a1, v1, b), VotedForIn(a2, v2, b)
             PROVE  v1 = v2
  OBVIOUS
<1>1. PICK m1 \in msgs : m1.type = "2b" /\ m1.val = v1 /\ m1.bal = b /\ m1.acc = a1
  BY DEF VotedForIn
<1>2. PICK m2 \in msgs : m2.type = "2b" /\ m2.val = v2 /\ m2.bal = b /\ m2.acc = a2
  BY DEF VotedForIn
<1>3. PICK ma1 \in msgs : ma1.type = "2a" /\ ma1.bal = b /\ ma1.val = v1
  BY <1>1 DEF MsgInv
<1>4. PICK ma2 \in msgs : ma2.type = "2a" /\ ma2.bal = b /\ ma2.val = v2
  BY <1>2 DEF MsgInv
<1>5. ma1 = ma2
  BY <1>3, <1>4 DEF MsgInv
<1> QED
  BY <1>3, <1>4, <1>5

(* maxBal never decreases. *)
LEMMA MaxBalMonotone ==
  ASSUME TypeOK, Next, NEW a \in Acceptors
  PROVE  maxBal'[a] >= maxBal[a]
<1> USE DEF TypeOK
<1>1. CASE \E bb \in Ballots : Phase1a(bb)
  BY <1>1 DEF Phase1a
<1>2. CASE \E bb \in Ballots : Phase2a(bb)
  BY <1>2 DEF Phase2a
<1>3. CASE \E aa \in Acceptors : Phase1b(aa)
  <2> PICK aa \in Acceptors : Phase1b(aa)
    BY <1>3
  <2> PICK m \in msgs : /\ m.bal > maxBal[aa]
                       /\ maxBal' = [maxBal EXCEPT ![aa] = m.bal]
    BY DEF Phase1b
  <2> QED
    BY SMTT(10)
<1>4. CASE \E aa \in Acceptors : Phase2b(aa)
  <2> PICK aa \in Acceptors : Phase2b(aa)
    BY <1>4
  <2> PICK m \in msgs : /\ m.bal >= maxBal[aa]
                       /\ maxBal' = [maxBal EXCEPT ![aa] = m.bal]
    BY DEF Phase2b
  <2> QED
    BY SMTT(10)
<1> QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(* No new votes are cast in a ballot c by an acceptor a once maxBal[a] > c. *)
LEMMA NewVoteBound ==
  ASSUME TypeOK, Next, NEW a \in Acceptors, NEW c \in Ballots, maxBal[a] > c,
         NEW w \in Values, VotedForIn(a, w, c)'
  PROVE  VotedForIn(a, w, c)
<1> USE DEF TypeOK
<1> PICK m \in msgs' : m.type = "2b" /\ m.val = w /\ m.bal = c /\ m.acc = a
  BY DEF VotedForIn
<1> SUFFICES m \in msgs
  BY DEF VotedForIn
<1>1. CASE \E bb \in Ballots : Phase1a(bb)
  BY <1>1 DEF Phase1a, Send
<1>2. CASE \E bb \in Ballots : Phase2a(bb)
  <2> PICK bb \in Ballots : Phase2a(bb)
    BY <1>2
  <2> PICK vv \in Values : msgs' = msgs \cup {[type |-> "2a", bal |-> bb, val |-> vv]}
    BY DEF Phase2a, Send
  <2> QED
    OBVIOUS
<1>3. CASE \E aa \in Acceptors : Phase1b(aa)
  <2> PICK aa \in Acceptors : Phase1b(aa)
    BY <1>3
  <2> PICK m1 \in msgs : msgs' = msgs \cup
         {[type |-> "1b", bal |-> m1.bal, maxVBal |-> maxVBal[aa],
           maxVal |-> maxVal[aa], acc |-> aa]}
    BY DEF Phase1b, Send
  <2> QED
    OBVIOUS
<1>4. CASE \E aa \in Acceptors : Phase2b(aa)
  <2> PICK aa \in Acceptors : Phase2b(aa)
    BY <1>4
  <2> PICK m0 \in msgs : /\ m0.type = "2a"
                        /\ m0.bal >= maxBal[aa]
                        /\ msgs' = msgs \cup
                             {[type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> aa]}
    BY DEF Phase2b, Send
  <2>1. CASE m \in msgs
    BY <2>1
  <2>2. CASE m \notin msgs
    <3>1. m = [type |-> "2b", bal |-> m0.bal, val |-> m0.val, acc |-> aa]
      BY <2>2
    <3>2. a = aa /\ c = m0.bal
      BY <3>1
    <3> QED
      BY <3>2, SMTT(10)
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(* SafeAt is stable: once it holds, it continues to hold. *)
LEMMA SafeAtStable ==
  ASSUME Inv, Next, TypeOK'
  PROVE  \A v \in Values, b \in Ballots : SafeAt(v, b) => SafeAt(v, b)'
<1> USE DEF Inv
<1> SUFFICES ASSUME NEW v \in Values, NEW b \in Ballots, SafeAt(v, b),
                    NEW c \in 0..(b-1)
             PROVE  \E Q \in Quorums : \A aa \in Q : VotedForIn(aa, v, c)' \/ WontVoteIn(aa, c)'
  BY DEF SafeAt
<1>0. c \in Ballots
  BY SMTT(10)
<1>1. PICK Q \in Quorums : \A aa \in Q : VotedForIn(aa, v, c) \/ WontVoteIn(aa, c)
  BY DEF SafeAt
<1>2. \A aa \in Q : VotedForIn(aa, v, c)' \/ WontVoteIn(aa, c)'
  <2> TAKE aa \in Q
  <2>1. aa \in Acceptors
    BY <1>1, QuorumAssumption
  <2>2. CASE VotedForIn(aa, v, c)
    BY <2>2, VotedForInStable
  <2>3. CASE WontVoteIn(aa, c)
    <3>1. maxBal[aa] > c
      BY <2>3 DEF WontVoteIn
    <3>2. \A w \in Values : ~ VotedForIn(aa, w, c)
      BY <2>3 DEF WontVoteIn
    <3>3. maxBal'[aa] >= maxBal[aa]
      BY <2>1, MaxBalMonotone
    <3>4. maxBal'[aa] > c
      BY <3>1, <3>3, <2>1, <1>0 DEF TypeOK
    <3>5. \A w \in Values : ~ VotedForIn(aa, w, c)'
      BY <2>1, <1>0, <3>1, <3>2, NewVoteBound
    <3> QED
      BY <3>4, <3>5 DEF WontVoteIn
  <2> QED
    BY <1>1, <2>2, <2>3
<1> QED
  BY <1>1, <1>2

(* The inductive invariant Inv is preserved by the specification. *)
THEOREM Invariant == Spec => []Inv
<1>1. Init => Inv
  BY NoneNotInValues
  DEF Init, Inv, TypeOK, Messages, MsgInv, AccInv, VotedForIn
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE vars' = vars
    BY <2>1 DEF vars, TypeOK, MsgInv, AccInv, VotedForIn, SafeAt, WontVoteIn
  <2>2. CASE \E b \in Ballots : Phase1a(b)
    <3> PICK b \in Ballots : Phase1a(b)
      BY <2>2
    <3>m. msgs' = msgs \cup {[type |-> "1a", bal |-> b]}
      BY DEF Phase1a, Send
    <3>u. maxVBal' = maxVBal /\ maxBal' = maxBal /\ maxVal' = maxVal
      BY DEF Phase1a
    <3>v. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
      BY <3>m DEF VotedForIn
    <3>s. \A vv, bb : SafeAt(vv, bb)' <=> SafeAt(vv, bb)
      BY <3>v, <3>u DEF SafeAt, WontVoteIn
    <3>1. TypeOK'
      BY <3>m, <3>u DEF TypeOK, Messages
    <3>2. MsgInv'
      BY <3>m, <3>u, <3>v, <3>s DEF MsgInv
    <3>3. AccInv'
      BY <3>u, <3>v DEF AccInv
    <3> QED
      BY <3>1, <3>2, <3>3 DEF Inv
  <2>3. CASE \E b \in Ballots : Phase2a(b)
    <3> PICK b \in Ballots : Phase2a(b)
      BY <2>3
    <3>next. Next
      BY <2>3 DEF Next
    <3>0. ~ \E mm \in msgs : (mm.type = "2a") /\ (mm.bal = b)
      BY DEF Phase2a
    <3>1. PICK v \in Values, Q \in Quorums,
               S \in SUBSET {mm \in msgs : (mm.type = "1b") /\ (mm.bal = b)} :
            /\ \A aa \in Q : \E mm \in S : mm.acc = aa
            /\ \/ \A mm \in S : mm.maxVBal = -1
               \/ \E c0 \in 0..(b-1) :
                     /\ \A mm \in S : mm.maxVBal =< c0
                     /\ \E mm \in S : mm.maxVBal = c0 /\ mm.maxVal = v
            /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
      BY DEF Phase2a, Send
    <3>u. maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
      BY DEF Phase2a
    <3>v. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
      BY <3>1 DEF VotedForIn
    <3>s. \A vv, bb : SafeAt(vv, bb)' <=> SafeAt(vv, bb)
      BY <3>v, <3>u DEF SafeAt, WontVoteIn
    <3>Sf. \A mm \in S : /\ mm \in msgs
                        /\ mm.type = "1b"
                        /\ mm.bal = b
                        /\ mm.acc \in Acceptors
                        /\ mm.maxVBal \in Ballots \cup {-1}
                        /\ mm.maxVal \in Values \cup {None}
      BY <3>1 DEF TypeOK, Messages
    <3>safe. SafeAt(v, b)
      <4> SUFFICES ASSUME NEW c \in 0..(b-1)
                   PROVE  \E QQ \in Quorums : \A aa \in QQ : VotedForIn(aa, v, c) \/ WontVoteIn(aa, c)
        BY DEF SafeAt
      <4>cb. c \in Ballots /\ 0 =< c /\ c =< b-1
        BY SMTT(10)
      <4>won. \A a2 \in Q, m1 \in S, cc \in 0..(b-1) :
                (m1.acc = a2 /\ cc > m1.maxVBal) => WontVoteIn(a2, cc)
        <5> TAKE a2 \in Q, m1 \in S, cc \in 0..(b-1)
        <5> SUFFICES ASSUME m1.acc = a2, cc > m1.maxVBal
                     PROVE  WontVoteIn(a2, cc)
          OBVIOUS
        <5>1. /\ m1 \in msgs /\ m1.type = "1b" /\ m1.bal = b /\ m1.acc = a2
              /\ m1.maxVBal \in Ballots \cup {-1}
              /\ a2 \in Acceptors
              /\ maxBal[a2] \in Ballots \cup {-1}
          BY <3>Sf, QuorumAssumption DEF TypeOK
        <5>mi. /\ m1.bal =< maxBal[m1.acc]
               /\ \A c2 \in (m1.maxVBal+1)..(m1.bal-1) :
                     ~ \E w \in Values : VotedForIn(m1.acc, w, c2)
          BY <5>1 DEF MsgInv
        <5>3. cc \in (m1.maxVBal+1)..(m1.bal-1)
          BY <5>1, SMTT(10)
        <5>4. ~ \E w \in Values : VotedForIn(a2, w, cc)
          BY <5>1, <5>mi, <5>3
        <5>5. maxBal[a2] > cc
          BY <5>1, <5>mi, SMTT(10)
        <5> QED
          BY <5>4, <5>5 DEF WontVoteIn
      <4>caseA. CASE \A mm \in S : mm.maxVBal = -1
        <5> SUFFICES \A aa \in Q : VotedForIn(aa, v, c) \/ WontVoteIn(aa, c)
          BY <3>1
        <5> TAKE aa \in Q
        <5>1. PICK m1 \in S : m1.acc = aa
          BY <3>1
        <5>2. m1.maxVBal = -1
          BY <5>1, <4>caseA
        <5>3. c > m1.maxVBal
          BY <5>2, <4>cb, SMTT(10)
        <5>4. WontVoteIn(aa, c)
          BY <4>won, <5>1, <5>3
        <5> QED
          BY <5>4
      <4>caseB. CASE \E c0 \in 0..(b-1) :
                        /\ \A mm \in S : mm.maxVBal =< c0
                        /\ \E mm \in S : mm.maxVBal = c0 /\ mm.maxVal = v
        <5>p0. PICK c0 \in 0..(b-1) :
                 /\ \A mm \in S : mm.maxVBal =< c0
                 /\ \E mm \in S : mm.maxVBal = c0 /\ mm.maxVal = v
          BY <4>caseB
        <5>c0. c0 \in Ballots /\ 0 =< c0 /\ c0 =< b-1
          BY SMTT(10)
        <5> PICK mstar \in S : mstar.maxVBal = c0 /\ mstar.maxVal = v
          BY <5>p0
        <5>star. VotedForIn(mstar.acc, v, c0)
          <6>1. /\ mstar \in msgs /\ mstar.type = "1b" /\ mstar.bal = b
                /\ mstar.acc \in Acceptors
                /\ mstar.maxVBal = c0 /\ mstar.maxVal = v
            BY <3>Sf
          <6>2. mstar.maxVBal \in Ballots
            BY <5>c0, <6>1, SMTT(10)
          <6>3. \/ /\ mstar.maxVal \in Values /\ mstar.maxVBal \in Ballots
                   /\ VotedForIn(mstar.acc, mstar.maxVal, mstar.maxVBal)
                \/ /\ mstar.maxVal = None /\ mstar.maxVBal = -1
            BY <6>1 DEF MsgInv
          <6>4. mstar.maxVBal # -1
            BY <5>c0, <6>1, SMTT(10)
          <6> QED
            BY <6>1, <6>3, <6>4
        <5>caseLt. CASE c < c0
          <6>1. mstar.acc \in Acceptors
            BY <3>Sf
          <6>2. SafeAt(v, c0)
            BY <5>star, <6>1, <5>c0, VotedInv DEF TypeOK, Inv
          <6>3. c \in 0..(c0-1)
            BY <4>cb, <5>caseLt, SMTT(10)
          <6> QED
            BY <6>2, <6>3 DEF SafeAt
        <5>caseGe. CASE c >= c0
          <6> SUFFICES \A aa \in Q : VotedForIn(aa, v, c) \/ WontVoteIn(aa, c)
            BY <3>1
          <6> TAKE aa \in Q
          <6>1. PICK m1 \in S : m1.acc = aa
            BY <3>1
          <6>m1. /\ m1 \in msgs /\ m1.type = "1b" /\ m1.bal = b /\ m1.acc = aa
                 /\ m1.maxVBal =< c0 /\ m1.maxVBal \in Ballots \cup {-1}
                 /\ m1.maxVal \in Values \cup {None}
                 /\ aa \in Acceptors
            BY <3>Sf, <5>p0, <6>1, QuorumAssumption
          <6>gt. CASE c > c0
            <7>1. c > m1.maxVBal
              BY <6>m1, <6>gt, <5>c0, SMTT(10)
            <7> QED
              BY <4>won, <6>1, <7>1
          <6>eq. CASE c = c0
            <7>lt. CASE m1.maxVBal < c0
              <8>1. c > m1.maxVBal
                BY <6>eq, <7>lt, SMTT(10)
              <8> QED
                BY <4>won, <6>1, <8>1
            <7>eq2. CASE m1.maxVBal = c0
              <8>1. m1.maxVBal \in Ballots
                BY <5>c0, <7>eq2, SMTT(10)
              <8>2. \/ /\ m1.maxVal \in Values /\ m1.maxVBal \in Ballots
                       /\ VotedForIn(aa, m1.maxVal, m1.maxVBal)
                    \/ /\ m1.maxVal = None /\ m1.maxVBal = -1
                BY <6>m1 DEF MsgInv
              <8>3. m1.maxVal \in Values /\ VotedForIn(aa, m1.maxVal, c0)
                BY <8>1, <8>2, <7>eq2, SMTT(10)
              <8>4. m1.maxVal = v
                BY <8>3, <5>star, <6>m1, <5>c0, <3>Sf, VotedOnce
              <8> QED
                BY <8>3, <8>4, <6>eq
            <7> QED
              BY <7>lt, <7>eq2, <6>m1, SMTT(10)
          <6> QED
            BY <6>gt, <6>eq, <5>caseGe, SMTT(10)
        <5> QED
          BY <5>caseLt, <5>caseGe
      <4> QED
        BY <4>caseA, <4>caseB, <3>1
    <3>1tok. TypeOK'
      BY <3>1, <3>u DEF TypeOK, Messages
    <3>2. MsgInv'
      BY <3>0, <3>1, <3>u, <3>v, <3>s, <3>safe DEF MsgInv, TypeOK, Messages
    <3>3. AccInv'
      BY <3>u, <3>v DEF AccInv
    <3> QED
      BY <3>1tok, <3>2, <3>3 DEF Inv
  <2>4. CASE \E a \in Acceptors : Phase1b(a)
    <3> PICK a \in Acceptors : Phase1b(a)
      BY <2>4
    <3>next. Next
      BY <2>4 DEF Next
    <3>1. PICK m \in msgs :
            /\ m.type = "1a"
            /\ m.bal > maxBal[a]
            /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
            /\ msgs' = msgs \cup {[type |-> "1b", bal |-> m.bal,
                          maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a]}
            /\ maxVBal' = maxVBal
            /\ maxVal' = maxVal
      BY DEF Phase1b, Send
    <3>v. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
      BY <3>1 DEF VotedForIn
    <3>1m. m.bal \in Ballots /\ maxBal[a] \in Ballots \cup {-1} /\ maxVBal[a] \in Ballots \cup {-1}
      BY <3>1 DEF TypeOK, Messages
    <3>1tok. TypeOK'
      BY <3>1, <3>1m, NoneNotInValues DEF TypeOK, Messages
    <3>safe. \A vv \in Values, bb \in Ballots : SafeAt(vv, bb) => SafeAt(vv, bb)'
      BY <3>next, <3>1tok, SafeAtStable
    <3>2. MsgInv'
      BY <3>1, <3>1m, <3>v, <3>safe DEF MsgInv, AccInv, TypeOK, Messages
    <3>3. AccInv'
      BY <3>1, <3>1m, <3>v DEF AccInv, TypeOK
    <3> QED
      BY <3>1tok, <3>2, <3>3 DEF Inv
  <2>5. CASE \E a \in Acceptors : Phase2b(a)
    <3> PICK a \in Acceptors : Phase2b(a)
      BY <2>5
    <3>next. Next
      BY <2>5 DEF Next
    <3>1. PICK m \in msgs :
            /\ m.type = "2a"
            /\ m.bal >= maxBal[a]
            /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
            /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
            /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
            /\ msgs' = msgs \cup {[type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]}
      BY DEF Phase2b, Send
    <3>1m. m.bal \in Ballots /\ m.val \in Values /\ maxBal[a] \in Ballots \cup {-1}
           /\ maxVBal[a] \in Ballots \cup {-1} /\ maxBal[a] >= maxVBal[a]
      BY <3>1 DEF TypeOK, Messages
    <3>v. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=>
            (VotedForIn(aa, vv, bb) \/ (aa = a /\ vv = m.val /\ bb = m.bal))
      BY <3>1 DEF VotedForIn
    <3>1tok. TypeOK'
      BY <3>1, <3>1m, NoneNotInValues DEF TypeOK, Messages
    <3>safe. \A vv \in Values, bb \in Ballots : SafeAt(vv, bb) => SafeAt(vv, bb)'
      BY <3>next, <3>1tok, SafeAtStable
    <3>2. MsgInv'
      BY <3>1, <3>1m, <3>v, <3>safe DEF MsgInv, TypeOK, Messages
    <3>3. AccInv'
      BY <3>1, <3>1m, <3>v, NoneNotInValues DEF AccInv, TypeOK, Messages
    <3> QED
      BY <3>1tok, <3>2, <3>3 DEF Inv
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

(* Two values chosen at ballots b1 =< b2 must be equal. *)
LEMMA ChosenSafe ==
  ASSUME Inv, NEW v1 \in Values, NEW v2 \in Values,
         NEW b1 \in Ballots, NEW b2 \in Ballots,
         ChosenIn(v1, b1), ChosenIn(v2, b2), b1 =< b2
  PROVE  v1 = v2
<1> USE DEF Inv
<1>1. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
  BY DEF ChosenIn
<1>2. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)
  BY DEF ChosenIn
<1>3. CASE b1 = b2
  <2>1. PICK a : a \in Q1 /\ a \in Q2
    BY <1>1, <1>2, QuorumAssumption
  <2>2. a \in Acceptors
    BY <2>1, <1>1, QuorumAssumption
  <2>3. VotedForIn(a, v1, b1) /\ VotedForIn(a, v2, b1)
    BY <2>1, <1>1, <1>2, <1>3
  <2> QED
    BY <2>2, <2>3, VotedOnce
<1>4. CASE b1 < b2
  <2>1. PICK a2 \in Q2 : VotedForIn(a2, v2, b2)
    BY <1>2, QuorumAssumption
  <2>2. a2 \in Acceptors
    BY <2>1, <1>2, QuorumAssumption
  <2>3. SafeAt(v2, b2)
    BY <2>1, <2>2, VotedInv
  <2>4. b1 \in 0..(b2-1)
    BY <1>4, SMTT(10)
  <2>5. PICK Q3 \in Quorums : \A a \in Q3 : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
    BY <2>3, <2>4 DEF SafeAt
  <2>6. PICK a : a \in Q1 /\ a \in Q3
    BY <1>1, <2>5, QuorumAssumption
  <2>7. /\ a \in Acceptors
        /\ VotedForIn(a, v1, b1)
        /\ (VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1))
    BY <2>6, <1>1, <2>5, QuorumAssumption
  <2>8. VotedForIn(a, v2, b1)
    BY <2>7 DEF WontVoteIn
  <2> QED
    BY <2>7, <2>8, VotedOnce
<1> QED
  BY <1>3, <1>4, SMTT(10)

(* The invariant implies consistency: at most one value is ever chosen. *)
LEMMA Consistent == Inv => Consistency
<1> SUFFICES ASSUME Inv, NEW v1 \in Values, NEW v2 \in Values, Chosen(v1), Chosen(v2)
             PROVE  v1 = v2
  BY DEF Consistency
<1>1. PICK b1 \in Ballots : ChosenIn(v1, b1)
  BY DEF Chosen
<1>2. PICK b2 \in Ballots : ChosenIn(v2, b2)
  BY DEF Chosen
<1>3. CASE b1 =< b2
  BY <1>1, <1>2, <1>3, ChosenSafe
<1>4. CASE b2 =< b1
  BY <1>1, <1>2, <1>4, ChosenSafe
<1> QED
  BY <1>3, <1>4, SMTT(10)
-----------------------------------------------------------------------------
IndInv == Inv /\ Consistency

THEOREM IndInvariant == Spec => []IndInv
<1>1. Inv => IndInv
  BY Consistent DEF IndInv
<1> QED
  BY Invariant, <1>1, PTL

THEOREM Refinement == Spec => C!Spec
<1>1. Init => C!Init
  BY QuorumAssumption
  DEF Init, C!Init, chosenBar, Chosen, ChosenIn, VotedForIn
<1>2. IndInv /\ IndInv' /\ [Next]_vars => [C!Next]_chosenBar
  <2> SUFFICES ASSUME IndInv, IndInv', [Next]_vars
               PROVE  [C!Next]_chosenBar
    OBVIOUS
  <2> USE DEF IndInv
  <2>mono. chosenBar \subseteq chosenBar'
    <3> SUFFICES ASSUME NEW x \in chosenBar PROVE x \in chosenBar'
      OBVIOUS
    <3>1. x \in Values /\ Chosen(x)
      BY DEF chosenBar
    <3>2. Chosen(x)'
      <4>1. PICK bb \in Ballots : ChosenIn(x, bb)
        BY <3>1 DEF Chosen
      <4>2. PICK QQ \in Quorums : \A aa \in QQ : VotedForIn(aa, x, bb)
        BY <4>1 DEF ChosenIn
      <4>3. \A aa \in QQ : VotedForIn(aa, x, bb)'
        BY <4>2, VotedForInStable
      <4>4. ChosenIn(x, bb)'
        BY <4>2, <4>3 DEF ChosenIn
      <4> QED
        BY <4>1, <4>4 DEF Chosen
    <3> QED
      BY <3>1, <3>2 DEF chosenBar
  <2>one. \A x, y \in chosenBar' : x = y
    <3> SUFFICES ASSUME NEW x \in chosenBar', NEW y \in chosenBar'
                 PROVE  x = y
      OBVIOUS
    <3>1. /\ x \in Values /\ Chosen(x)'
          /\ y \in Values /\ Chosen(y)'
      BY DEF chosenBar
    <3> QED
      BY <3>1 DEF Consistency
  <2>sub. chosenBar' \subseteq Values
    BY DEF chosenBar
  <2> QED
    <3>1. CASE chosenBar' = chosenBar
      BY <3>1
    <3>2. CASE chosenBar' # chosenBar
      <4>1. PICK x : x \in chosenBar' /\ x \notin chosenBar
        BY <2>mono, <3>2
      <4>2. chosenBar' = {x}
        BY <4>1, <2>one
      <4>3. chosenBar = {}
        BY <4>1, <4>2, <2>mono
      <4>4. x \in Values
        BY <4>1, <2>sub
      <4>5. C!Next
        BY <4>2, <4>3, <4>4 DEF C!Next
      <4> QED
        BY <4>5
    <3> QED
      BY <3>1, <3>2
<1> QED
  BY <1>1, <1>2, IndInvariant, PTL DEF Spec, C!Spec
=============================================================================
\* Modification History
\* Last modified Sun Aug 04 10:59:26 CST 2019 by hengxin
\* Last modified Mon Jul 22 20:30:39 CST 2019 by hengxin
\* Last modified Fri Nov 28 10:39:17 PST 2014 by lamport
\* Last modified Sun Nov 23 14:45:09 PST 2014 by lamport
\* Last modified Mon Nov 24 02:03:02 CET 2014 by merz
\* Last modified Sat Nov 22 12:04:19 CET 2014 by merz
\* Last modified Fri Nov 21 17:40:41 PST 2014 by lamport
\* Last modified Tue Mar 18 11:37:57 CET 2014 by doligez
\* Last modified Sat Nov 24 18:53:09 GMT-03:00 2012 by merz
\* Created Sat Nov 17 16:02:06 PST 2012 by lamport