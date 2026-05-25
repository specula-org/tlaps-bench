------------------------------- MODULE Paxos_Consistent -------------------------------
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
(***************************************************************************)
(* Basic structural facts about messages.                                  *)
(***************************************************************************)

LEMMA MsgsStable ==
  ASSUME [Next]_vars
  PROVE  msgs \subseteq msgs'
BY DEF Next, Phase1a, Phase1b, Phase2a, Phase2b, Send, vars

LEMMA VotedForInStable ==
  ASSUME [Next]_vars,
         NEW a \in Acceptors, NEW v \in Values, NEW b \in Ballots,
         VotedForIn(a, v, b)
  PROVE  VotedForIn(a, v, b)'
BY MsgsStable DEF VotedForIn

LEMMA VotedInv ==
  MsgInv /\ TypeOK =>
    \A a \in Acceptors, v \in Values, b \in Ballots :
        VotedForIn(a, v, b) => SafeAt(v, b)
BY DEF VotedForIn, MsgInv, TypeOK, Messages, Ballots

LEMMA VotedOnce ==
  MsgInv => \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
                 VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
BY DEF MsgInv, VotedForIn

LEMMA NoneNotInValues == None \notin Values
<1>1. \E v : v \notin Values  BY NoSetContainsEverything
<1> QED  BY <1>1 DEF None

(***************************************************************************)
(* A new vote (a 2b message) for acceptor aa in ballot cc can only be       *)
(* created by Phase2b(aa) firing on a 2a message of ballot cc, and that     *)
(* ballot is at least maxBal[aa].                                           *)
(***************************************************************************)
LEMMA VoteCreation ==
  ASSUME Inv, [Next]_vars,
         NEW aa \in Acceptors, NEW vv \in Values, NEW cc \in Ballots,
         ~VotedForIn(aa, vv, cc), VotedForIn(aa, vv, cc)'
  PROVE  /\ cc >= maxBal[aa]
         /\ maxVBal'[aa] = cc
<1> USE DEF Inv, Ballots
<1>1. PICK m \in msgs' : /\ m.type = "2b" /\ m.val = vv
                        /\ m.bal = cc /\ m.acc = aa
  BY DEF VotedForIn
<1>2. m \notin msgs
  BY <1>1 DEF VotedForIn
<1>3. CASE vars' = vars
  BY <1>2, <1>3 DEF vars
<1>4. ASSUME NEW bb \in Ballots, Phase1a(bb)  PROVE FALSE
  BY <1>1, <1>2, <1>4 DEF Phase1a, Send
<1>5. ASSUME NEW a2 \in Acceptors, Phase1b(a2)  PROVE FALSE
  BY <1>1, <1>2, <1>5 DEF Phase1b, Send
<1>6. ASSUME NEW bb \in Ballots, Phase2a(bb)  PROVE FALSE
  BY <1>1, <1>2, <1>6 DEF Phase2a, Send
<1>7. ASSUME NEW a2 \in Acceptors, Phase2b(a2)
      PROVE  cc >= maxBal[aa] /\ maxVBal'[aa] = cc
  <2>1. PICK m2 \in msgs : /\ m2.type = "2a"
                          /\ m2.bal >= maxBal[a2]
                          /\ maxVBal' = [maxVBal EXCEPT ![a2] = m2.bal]
                          /\ Send([type |-> "2b", bal |-> m2.bal,
                                   val |-> m2.val, acc |-> a2])
    BY <1>7 DEF Phase2b
  <2>2. m = [type |-> "2b", bal |-> m2.bal, val |-> m2.val, acc |-> a2]
    BY <1>1, <1>2, <2>1 DEF Send
  <2>3. a2 = aa /\ m2.bal = cc  BY <2>2, <1>1
  <2>4. maxBal[a2] \in Ballots \cup {-1}  BY DEF TypeOK
  <2>5. m2.bal \in Ballots  BY <2>1 DEF TypeOK, Messages
  <2>6. cc >= maxBal[aa]  BY <2>1, <2>3, <2>4, <2>5
  <2>7. maxVBal'[aa] = cc  BY <2>1, <2>3 DEF TypeOK
  <2> QED  BY <2>6, <2>7
<1> QED
  BY <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next

LEMMA MaxBalMonotone ==
  ASSUME TypeOK, [Next]_vars, NEW a \in Acceptors
  PROVE  maxBal[a] =< maxBal'[a]
<1>t. maxBal[a] \in Ballots \cup {-1}  BY DEF TypeOK
<1>1. CASE vars' = vars
  BY <1>1, <1>t DEF vars, Ballots
<1>2. CASE \E b \in Ballots : Phase1a(b)
  BY <1>2, <1>t DEF Phase1a, Ballots
<1>3. CASE \E b \in Ballots : Phase2a(b)
  BY <1>3, <1>t DEF Phase2a, Ballots
<1>4. CASE \E aa \in Acceptors : Phase1b(aa)
  <2>1. PICK aa \in Acceptors : Phase1b(aa)  BY <1>4
  <2>2. PICK m \in msgs : /\ m.type = "1a"
                         /\ m.bal > maxBal[aa]
                         /\ maxBal' = [maxBal EXCEPT ![aa] = m.bal]
    BY <2>1 DEF Phase1b
  <2>3. m.bal \in Ballots  BY <2>2 DEF TypeOK, Messages
  <2>4. maxBal[aa] \in Ballots \cup {-1}  BY <2>1 DEF TypeOK
  <2> QED  BY <2>2, <2>3, <2>4, <1>t DEF TypeOK, Ballots
<1>5. CASE \E aa \in Acceptors : Phase2b(aa)
  <2>1. PICK aa \in Acceptors : Phase2b(aa)  BY <1>5
  <2>2. PICK m \in msgs : /\ m.type = "2a"
                         /\ m.bal >= maxBal[aa]
                         /\ maxBal' = [maxBal EXCEPT ![aa] = m.bal]
    BY <2>1 DEF Phase2b
  <2>3. m.bal \in Ballots  BY <2>2 DEF TypeOK, Messages
  <2>4. maxBal[aa] \in Ballots \cup {-1}  BY <2>1 DEF TypeOK
  <2> QED  BY <2>2, <2>3, <2>4, <1>t DEF TypeOK, Ballots
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

LEMMA MaxVBalMonotone ==
  ASSUME TypeOK, [Next]_vars, NEW a \in Acceptors
  PROVE  maxVBal[a] =< maxVBal'[a]
<1>t. maxVBal[a] \in Ballots \cup {-1}  BY DEF TypeOK
<1>1. CASE vars' = vars
  BY <1>1, <1>t DEF vars, Ballots
<1>2. CASE \E b \in Ballots : Phase1a(b)
  BY <1>2, <1>t DEF Phase1a, Ballots
<1>3. CASE \E b \in Ballots : Phase2a(b)
  BY <1>3, <1>t DEF Phase2a, Ballots
<1>4. CASE \E aa \in Acceptors : Phase1b(aa)
  BY <1>4, <1>t DEF Phase1b, Ballots
<1>5. CASE \E aa \in Acceptors : Phase2b(aa)
  <2>1. PICK aa \in Acceptors : Phase2b(aa)  BY <1>5
  <2>2. PICK m \in msgs : /\ m.type = "2a"
                         /\ m.bal >= maxBal[aa]
                         /\ maxVBal' = [maxVBal EXCEPT ![aa] = m.bal]
    BY <2>1 DEF Phase2b
  <2>3. m.bal \in Ballots  BY <2>2 DEF TypeOK, Messages
  <2>4. maxBal[aa] >= maxVBal[aa] /\ maxVBal[aa] \in Ballots \cup {-1}
    BY <2>1 DEF TypeOK
  <2> QED  BY <2>2, <2>3, <2>4, <1>t DEF TypeOK, Ballots
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

(***************************************************************************)
(* Type correctness is preserved by every step.                           *)
(***************************************************************************)
LEMMA TypeOKInvariant ==
  ASSUME TypeOK, [Next]_vars  PROVE TypeOK'
<1> USE DEF Ballots
<1>1. CASE vars' = vars
  BY <1>1 DEF vars, TypeOK
<1>2. ASSUME NEW b \in Ballots, Phase1a(b)  PROVE TypeOK'
  <2>1. msgs' = msgs \cup {[type |-> "1a", bal |-> b]}
    BY <1>2 DEF Phase1a, Send
  <2>2. [type |-> "1a", bal |-> b] \in Messages  BY DEF Messages
  <2>3. UNCHANGED <<maxVBal, maxBal, maxVal>>  BY <1>2 DEF Phase1a
  <2> QED  BY <2>1, <2>2, <2>3 DEF TypeOK
<1>3. ASSUME NEW b \in Ballots, Phase2a(b)  PROVE TypeOK'
  <2>1. PICK v \in Values :
            Send([type |-> "2a", bal |-> b, val |-> v])
    BY <1>3 DEF Phase2a
  <2>2. msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
    BY <2>1 DEF Send
  <2>3. [type |-> "2a", bal |-> b, val |-> v] \in Messages  BY DEF Messages
  <2>4. UNCHANGED <<maxBal, maxVBal, maxVal>>  BY <1>3 DEF Phase2a
  <2> QED  BY <2>2, <2>3, <2>4 DEF TypeOK
<1>4. ASSUME NEW a \in Acceptors, Phase1b(a)  PROVE TypeOK'
  <2>1. PICK m \in msgs : /\ m.type = "1a"
                         /\ m.bal > maxBal[a]
                         /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                         /\ Send([type |-> "1b", bal |-> m.bal,
                                  maxVBal |-> maxVBal[a], maxVal |-> maxVal[a],
                                  acc |-> a])
                         /\ UNCHANGED <<maxVBal, maxVal>>
    BY <1>4 DEF Phase1b
  <2>2. m.bal \in Ballots  BY <2>1 DEF TypeOK, Messages
  <2>3. msgs' = msgs \cup {[type |-> "1b", bal |-> m.bal,
                            maxVBal |-> maxVBal[a], maxVal |-> maxVal[a],
                            acc |-> a]}
    BY <2>1 DEF Send
  <2>4. [type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a],
         maxVal |-> maxVal[a], acc |-> a] \in Messages
    BY <2>2 DEF Messages, TypeOK
  <2>5. maxBal' \in [Acceptors -> Ballots \cup {-1}]
    BY <2>1, <2>2 DEF TypeOK
  <2>6. \A aa \in Acceptors : maxBal'[aa] >= maxVBal'[aa]
    <3> SUFFICES ASSUME NEW aa \in Acceptors PROVE maxBal'[aa] >= maxVBal'[aa]
      OBVIOUS
    <3>1. maxVBal'[aa] = maxVBal[aa]  BY <2>1 DEF TypeOK
    <3>2. CASE aa = a
      <4>1. maxBal'[aa] = m.bal  BY <2>1, <3>2 DEF TypeOK
      <4>2. maxBal[a] >= maxVBal[a]  BY DEF TypeOK
      <4>3. maxBal[a] \in Ballots \cup {-1} /\ maxVBal[a] \in Ballots \cup {-1}
        BY DEF TypeOK
      <4> QED  BY <2>1, <2>2, <3>1, <3>2, <4>1, <4>2, <4>3
    <3>3. CASE aa # a
      <4>1. maxBal'[aa] = maxBal[aa]  BY <2>1, <3>3 DEF TypeOK
      <4> QED  BY <3>1, <4>1 DEF TypeOK
    <3> QED  BY <3>2, <3>3
  <2> QED  BY <2>1, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
<1>5. ASSUME NEW a \in Acceptors, Phase2b(a)  PROVE TypeOK'
  <2>1. PICK m \in msgs : /\ m.type = "2a"
                         /\ m.bal >= maxBal[a]
                         /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
                         /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                         /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
                         /\ Send([type |-> "2b", bal |-> m.bal,
                                  val |-> m.val, acc |-> a])
    BY <1>5 DEF Phase2b
  <2>2. m.bal \in Ballots /\ m.val \in Values  BY <2>1 DEF TypeOK, Messages
  <2>3. msgs' = msgs \cup {[type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]}
    BY <2>1 DEF Send
  <2>4. [type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a] \in Messages
    BY <2>2 DEF Messages
  <2>5. maxBal' \in [Acceptors -> Ballots \cup {-1}]
    BY <2>1, <2>2 DEF TypeOK
  <2>6. maxVBal' \in [Acceptors -> Ballots \cup {-1}]
    BY <2>1, <2>2 DEF TypeOK
  <2>7. maxVal' \in [Acceptors -> Values \cup {None}]
    BY <2>1, <2>2 DEF TypeOK
  <2>8. \A aa \in Acceptors : maxBal'[aa] >= maxVBal'[aa]
    <3> SUFFICES ASSUME NEW aa \in Acceptors PROVE maxBal'[aa] >= maxVBal'[aa]
      OBVIOUS
    <3>1. CASE aa = a
      BY <2>1, <2>2, <3>1 DEF TypeOK
    <3>2. CASE aa # a
      <4>1. maxBal'[aa] = maxBal[aa] /\ maxVBal'[aa] = maxVBal[aa]
        BY <2>1, <3>2 DEF TypeOK
      <4> QED  BY <4>1 DEF TypeOK
    <3> QED  BY <3>1, <3>2
  <2> QED  BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF TypeOK
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

LEMMA SafeAtStable ==
  ASSUME Inv, [Next]_vars, TypeOK',
         NEW v \in Values, NEW b \in Ballots, SafeAt(v, b)
  PROVE  SafeAt(v, b)'
<1> USE DEF Ballots, Inv
<1> SUFFICES ASSUME NEW c \in 0..(b-1)
             PROVE  \E Q \in Quorums :
                       \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
  BY DEF SafeAt
<1>c. c \in Ballots
  OBVIOUS
<1>1. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
  BY DEF SafeAt
<1>2. ASSUME NEW a \in Q
      PROVE  VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
  <2>a. a \in Acceptors
    BY <1>2, QuorumAssumption
  <2>1. CASE VotedForIn(a, v, c)
    BY <2>1, VotedForInStable, <2>a, <1>c
  <2>2. CASE WontVoteIn(a, c)
    <3>1. maxBal[a] > c  BY <2>2 DEF WontVoteIn
    <3>2. \A vv \in Values : ~VotedForIn(a, vv, c)  BY <2>2 DEF WontVoteIn
    <3>3. maxBal'[a] > c
      BY <3>1, MaxBalMonotone, <2>a DEF TypeOK
    <3>4. \A vv \in Values : ~VotedForIn(a, vv, c)'
      <4> SUFFICES ASSUME NEW vv \in Values, VotedForIn(a, vv, c)'
                   PROVE  FALSE
        OBVIOUS
      <4>1. PICK m \in msgs' : /\ m.type = "2b" /\ m.val = vv
                              /\ m.bal = c /\ m.acc = a
        BY DEF VotedForIn
      <4>2. m \notin msgs
        BY <3>2, <4>1 DEF VotedForIn
      <4>3. CASE vars' = vars
        BY <4>2, <4>3 DEF vars
      <4>4. ASSUME NEW bb \in Ballots, Phase1a(bb)
            PROVE  FALSE
        BY <4>1, <4>2, <4>4 DEF Phase1a, Send
      <4>5. ASSUME NEW aa \in Acceptors, Phase1b(aa)
            PROVE  FALSE
        BY <4>1, <4>2, <4>5 DEF Phase1b, Send
      <4>6. ASSUME NEW bb \in Ballots, Phase2a(bb)
            PROVE  FALSE
        BY <4>1, <4>2, <4>6 DEF Phase2a, Send
      <4>7. ASSUME NEW aa \in Acceptors, Phase2b(aa)
            PROVE  FALSE
        <5>1. PICK m2 \in msgs : /\ m2.type = "2a"
                                /\ m2.bal >= maxBal[aa]
                                /\ Send([type |-> "2b", bal |-> m2.bal,
                                         val |-> m2.val, acc |-> aa])
          BY <4>7 DEF Phase2b
        <5>2. m = [type |-> "2b", bal |-> m2.bal, val |-> m2.val, acc |-> aa]
          BY <4>1, <4>2, <5>1 DEF Send
        <5>3. aa = a /\ m2.bal = c
          BY <5>2, <4>1
        <5>4. maxBal[aa] \in Ballots \cup {-1}  BY <2>a, <5>3 DEF TypeOK
        <5>5. m2.bal \in Ballots  BY <5>1 DEF TypeOK, Messages
        <5> QED
          BY <3>1, <5>1, <5>3, <5>4, <5>5
      <4> QED
        BY <4>3, <4>4, <4>5, <4>6, <4>7 DEF Next
    <3> QED  BY <3>3, <3>4 DEF WontVoteIn
  <2> QED  BY <1>1, <1>2, <2>1, <2>2
<1> QED
  BY <1>2

(***************************************************************************)
(* The key lemma underlying Phase2a: the quorum of 1b messages collected   *)
(* by Phase2a establishes that the chosen value is safe at the ballot.     *)
(***************************************************************************)
LEMMA ShowsSafeAt ==
  ASSUME TypeOK, MsgInv, AccInv,
         NEW b \in Ballots, NEW v \in Values, NEW Q \in Quorums,
         NEW S \in SUBSET {mm \in msgs : (mm.type = "1b") /\ (mm.bal = b)},
         \A aa \in Q : \E mm \in S : mm.acc = aa,
         \/ \A mm \in S : mm.maxVBal = -1
         \/ \E cc \in 0..(b-1) :
               /\ \A mm \in S : mm.maxVBal =< cc
               /\ \E mm \in S : /\ mm.maxVBal = cc
                                /\ mm.maxVal = v
  PROVE  SafeAt(v, b)
<1> USE DEF Ballots
<1>q. \A aa \in Q : aa \in Acceptors  BY QuorumAssumption
<1>qt. \A aa \in Q : maxBal[aa] \in Ballots \cup {-1}  BY <1>q DEF TypeOK
<1>s. \A mm \in S : /\ mm \in msgs
                   /\ mm.type = "1b"
                   /\ mm.bal = b
                   /\ mm.acc \in Acceptors
                   /\ mm.maxVBal \in Ballots \cup {-1}
  BY DEF TypeOK, Messages
<1>m. \A mm \in S : /\ mm.bal =< maxBal[mm.acc]
                   /\ \A cc \in (mm.maxVBal+1)..(mm.bal-1) :
                          ~ \E vv \in Values : VotedForIn(mm.acc, vv, cc)
  BY <1>s DEF MsgInv
<1>mv. \A mm \in S : mm.maxVBal >= 0 =>
                       /\ mm.maxVal \in Values
                       /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
  BY <1>s DEF MsgInv
<1> SUFFICES ASSUME NEW c \in 0..(b-1)
             PROVE  \E QQ \in Quorums :
                       \A aa \in QQ : VotedForIn(aa, v, c) \/ WontVoteIn(aa, c)
  BY DEF SafeAt
<1>cb. c \in Ballots /\ c >= 0 /\ c =< b - 1  OBVIOUS
<1>A. CASE \A mm \in S : mm.maxVBal = -1
  <2>1. \A aa \in Q : WontVoteIn(aa, c)
    <3> SUFFICES ASSUME NEW aa \in Q PROVE WontVoteIn(aa, c)  OBVIOUS
    <3>1. PICK mm \in S : mm.acc = aa  OBVIOUS
    <3>2. mm.maxVBal = -1  BY <1>A, <3>1
    <3>3. mm.bal =< maxBal[mm.acc]  BY <1>m, <3>1
    <3>4. maxBal[aa] >= b  BY <3>1, <3>3, <1>s
    <3>5. maxBal[aa] > c  BY <3>4, <1>cb, <1>qt DEF Ballots
    <3>6. \A vv \in Values : ~VotedForIn(aa, vv, c)
      <4>1. \A cc \in 0..(b-1) : ~ \E vv \in Values : VotedForIn(aa, vv, cc)
        BY <1>m, <3>1, <3>2, <1>s
      <4> QED  BY <4>1, <1>cb
    <3> QED  BY <3>5, <3>6 DEF WontVoteIn
  <2> QED  BY <2>1
<1>B. CASE \E cc \in 0..(b-1) :
               /\ \A mm \in S : mm.maxVBal =< cc
               /\ \E mm \in S : /\ mm.maxVBal = cc
                                /\ mm.maxVal = v
  <2>0. PICK c0 \in 0..(b-1) :
            /\ \A mm \in S : mm.maxVBal =< c0
            /\ \E mm \in S : /\ mm.maxVBal = c0
                             /\ mm.maxVal = v
    BY <1>B
  <2>1. PICK m0 \in S : m0.maxVBal = c0 /\ m0.maxVal = v
    BY <2>0
  <2>c0. c0 \in Ballots /\ c0 >= 0 /\ c0 =< b - 1  BY <2>0
  <2>2. VotedForIn(m0.acc, v, c0)
    BY <2>1, <2>c0, <1>mv
  <2>3. m0.acc \in Acceptors  BY <2>1, <1>s
  <2>4. SafeAt(v, c0)
    BY <2>2, <2>3, <2>c0, VotedInv
  <2>5. CASE c < c0
    <3>1. c \in 0..(c0-1)  BY <2>5, <2>c0, <1>cb
    <3> QED  BY <2>4, <3>1 DEF SafeAt
  <2>6. CASE c >= c0
    <3>1. \A aa \in Q : VotedForIn(aa, v, c) \/ WontVoteIn(aa, c)
      <4> SUFFICES ASSUME NEW aa \in Q
                   PROVE  VotedForIn(aa, v, c) \/ WontVoteIn(aa, c)
        OBVIOUS
      <4>1. PICK mm \in S : mm.acc = aa  OBVIOUS
      <4>2. mm.maxVBal =< c0  BY <2>0, <4>1
      <4>3. mm.bal = b /\ mm.bal =< maxBal[mm.acc]  BY <1>s, <1>m, <4>1
      <4>v. mm.maxVBal \in Ballots \cup {-1}  BY <1>s, <4>1
      <4>4. CASE mm.maxVBal = c
        <5>1. mm.maxVBal >= 0  BY <4>4, <2>6, <2>c0
        <5>2. mm.maxVal \in Values /\ VotedForIn(aa, mm.maxVal, mm.maxVBal)
          BY <4>1, <5>1, <1>mv
        <5>3. VotedForIn(aa, mm.maxVal, c)  BY <5>2, <4>4
        <5>4. c = c0  BY <4>2, <4>4, <2>6, <2>c0, <1>cb, <4>v
        <5>5. VotedForIn(m0.acc, v, c)  BY <2>2, <5>4
        <5>6. mm.maxVal = v
          BY <5>3, <5>5, <2>3, <1>q, <5>2, <1>cb, VotedOnce
        <5> QED  BY <5>3, <5>6
      <4>5. CASE mm.maxVBal # c
        <5>1. mm.maxVBal < c  BY <4>2, <4>5, <2>6, <2>c0, <1>cb, <4>v
        <5>2. maxBal[aa] >= b  BY <4>3, <4>1
        <5>3. maxBal[aa] > c  BY <5>2, <1>cb, <1>qt DEF Ballots
        <5>4. \A vv \in Values : ~VotedForIn(aa, vv, c)
          <6>1. c \in (mm.maxVBal+1)..(mm.bal-1)
            BY <5>1, <4>3, <1>cb, <4>v
          <6> QED  BY <6>1, <1>m, <4>1
        <5> QED  BY <5>3, <5>4 DEF WontVoteIn
      <4> QED  BY <4>4, <4>5
    <3> QED  BY <3>1
  <2> QED  BY <2>5, <2>6, <1>cb
<1> QED  BY <1>A, <1>B

(***************************************************************************)
(* The acceptor invariant is preserved by every step.                     *)
(***************************************************************************)
LEMMA AccInvInvariant ==
  ASSUME Inv, [Next]_vars  PROVE AccInv'
<1> USE DEF Inv, Ballots
<1>type. TypeOK'  BY TypeOKInvariant
<1> SUFFICES ASSUME NEW a \in Acceptors
             PROVE  /\ (maxVal'[a] = None) <=> (maxVBal'[a] = -1)
                    /\ maxVBal'[a] =< maxBal'[a]
                    /\ (maxVBal'[a] >= 0) =>
                          VotedForIn(a, maxVal[a], maxVBal[a])'
                    /\ \A c \in Ballots : c > maxVBal'[a] =>
                          ~ \E v \in Values : VotedForIn(a, v, c)'
  BY DEF AccInv
(* Conjunct 2 is exactly type correctness. *)
<1>c2. maxVBal'[a] =< maxBal'[a]  BY <1>type DEF TypeOK
(* Conjunct 4 holds uniformly, using monotonicity of maxVBal and the fact   *)
(* that a fresh vote sets maxVBal to its ballot.                            *)
<1>c4. \A c \in Ballots : c > maxVBal'[a] =>
          ~ \E v \in Values : VotedForIn(a, v, c)'
  <2> SUFFICES ASSUME NEW c \in Ballots, c > maxVBal'[a],
                      NEW v \in Values, VotedForIn(a, v, c)'
               PROVE  FALSE
    OBVIOUS
  <2>1. CASE VotedForIn(a, v, c)
    <3>1. maxVBal[a] =< maxVBal'[a]  BY MaxVBalMonotone
    <3>2. maxVBal[a] \in Ballots \cup {-1}  BY DEF TypeOK
    <3>3. maxVBal'[a] \in Ballots \cup {-1}  BY <1>type DEF TypeOK
    <3>4. c > maxVBal[a]  BY <3>1, <3>2, <3>3
    <3> QED  BY <3>4, <2>1 DEF AccInv
  <2>2. CASE ~VotedForIn(a, v, c)
    <3>1. maxVBal'[a] = c  BY <2>2, VoteCreation
    <3> QED  BY <3>1
  <2> QED  BY <2>1, <2>2
(* Conjuncts 1 and 3 require a case analysis on the step. *)
<1>U. ASSUME maxVal'[a] = maxVal[a], maxVBal'[a] = maxVBal[a]
      PROVE  /\ (maxVal'[a] = None) <=> (maxVBal'[a] = -1)
             /\ (maxVBal'[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
  <2>1. (maxVal'[a] = None) <=> (maxVBal'[a] = -1)  BY <1>U DEF AccInv
  <2>2. (maxVBal'[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
    <3> SUFFICES ASSUME maxVBal'[a] >= 0
                 PROVE  VotedForIn(a, maxVal[a], maxVBal[a])'
      OBVIOUS
    <3>1. maxVBal[a] >= 0  BY <1>U
    <3>2. VotedForIn(a, maxVal[a], maxVBal[a])  BY <3>1 DEF AccInv
    <3>3. msgs \subseteq msgs'  BY MsgsStable
    <3> QED  BY <3>2, <3>3, <1>U DEF VotedForIn
  <2> QED  BY <2>1, <2>2
<1>c13. /\ (maxVal'[a] = None) <=> (maxVBal'[a] = -1)
        /\ (maxVBal'[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
  <2>1. CASE vars' = vars
    <3>1. maxVal'[a] = maxVal[a] /\ maxVBal'[a] = maxVBal[a]  BY <2>1 DEF vars
    <3> QED  BY <3>1, <1>U
  <2>2. ASSUME NEW b \in Ballots, Phase1a(b)
        PROVE  /\ (maxVal'[a] = None) <=> (maxVBal'[a] = -1)
               /\ (maxVBal'[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
    <3>1. maxVal'[a] = maxVal[a] /\ maxVBal'[a] = maxVBal[a]  BY <2>2 DEF Phase1a
    <3> QED  BY <3>1, <1>U
  <2>3. ASSUME NEW b \in Ballots, Phase2a(b)
        PROVE  /\ (maxVal'[a] = None) <=> (maxVBal'[a] = -1)
               /\ (maxVBal'[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
    <3>1. maxVal'[a] = maxVal[a] /\ maxVBal'[a] = maxVBal[a]  BY <2>3 DEF Phase2a
    <3> QED  BY <3>1, <1>U
  <2>4. ASSUME NEW a2 \in Acceptors, Phase1b(a2)
        PROVE  /\ (maxVal'[a] = None) <=> (maxVBal'[a] = -1)
               /\ (maxVBal'[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
    <3>1. maxVal'[a] = maxVal[a] /\ maxVBal'[a] = maxVBal[a]  BY <2>4 DEF Phase1b
    <3> QED  BY <3>1, <1>U
  <2>5. ASSUME NEW a2 \in Acceptors, Phase2b(a2)
        PROVE  /\ (maxVal'[a] = None) <=> (maxVBal'[a] = -1)
               /\ (maxVBal'[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
    <3>0. PICK m \in msgs : /\ m.type = "2a"
                           /\ m.bal >= maxBal[a2]
                           /\ maxVBal' = [maxVBal EXCEPT ![a2] = m.bal]
                           /\ maxVal' = [maxVal EXCEPT ![a2] = m.val]
                           /\ msgs' = msgs \cup {[type |-> "2b", bal |-> m.bal,
                                                  val |-> m.val, acc |-> a2]}
      BY <2>5 DEF Phase2b, Send
    <3>1. CASE a # a2
      <4>1. maxVal'[a] = maxVal[a] /\ maxVBal'[a] = maxVBal[a]
        BY <3>0, <3>1 DEF TypeOK
      <4> QED  BY <4>1, <1>U
    <3>2. CASE a = a2
      <4>m. m.bal \in Ballots /\ m.val \in Values  BY <3>0 DEF TypeOK, Messages
      <4>1. maxVal'[a] = m.val /\ maxVBal'[a] = m.bal  BY <3>0, <3>2 DEF TypeOK
      <4>2. (maxVal'[a] = None) <=> (maxVBal'[a] = -1)
        BY <4>1, <4>m, NoneNotInValues
      <4>3. (maxVBal'[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])'
        <5> SUFFICES ASSUME maxVBal'[a] >= 0
                     PROVE  VotedForIn(a, maxVal[a], maxVBal[a])'
          OBVIOUS
        <5>1. [type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a2] \in msgs'
          BY <3>0
        <5>2. maxVal'[a] = m.val /\ maxVBal'[a] = m.bal /\ a = a2
          BY <4>1, <3>2
        <5> QED  BY <5>1, <5>2 DEF VotedForIn
      <4> QED  BY <4>2, <4>3
    <3> QED  BY <3>1, <3>2
  <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1> QED  BY <1>c2, <1>c4, <1>c13

(***************************************************************************)
(* The message invariant is preserved by every step.                      *)
(***************************************************************************)
LEMMA MsgInvInvariant ==
  ASSUME Inv, [Next]_vars  PROVE MsgInv'
<1> USE DEF Inv, Ballots
<1>type. TypeOK'  BY TypeOKInvariant
<1>accP. AccInv'  BY AccInvInvariant
<1>sub. msgs \subseteq msgs'  BY MsgsStable
(* 2a uniqueness across the step. *)
<1>uniq. \A m1, m2 \in msgs' :
            (m1.type = "2a") /\ (m2.type = "2a") /\ (m1.bal = m2.bal) => (m1 = m2)
  <2> SUFFICES ASSUME NEW m1 \in msgs', NEW m2 \in msgs',
                      m1.type = "2a", m2.type = "2a", m1.bal = m2.bal
               PROVE  m1 = m2
    OBVIOUS
  <2>1. CASE vars' = vars
    <3>1. m1 \in msgs /\ m2 \in msgs  BY <2>1 DEF vars
    <3> QED  BY <3>1 DEF MsgInv
  <2>2. ASSUME NEW b \in Ballots, Phase1a(b)  PROVE m1 = m2
    <3>1. msgs' = msgs \cup {[type |-> "1a", bal |-> b]}  BY <2>2 DEF Phase1a, Send
    <3>2. m1 \in msgs /\ m2 \in msgs  BY <3>1
    <3> QED  BY <3>2 DEF MsgInv
  <2>3. ASSUME NEW aa \in Acceptors, Phase1b(aa)  PROVE m1 = m2
    <3>1. PICK mp \in msgs :
              msgs' = msgs \cup {[type |-> "1b", bal |-> mp.bal,
                                  maxVBal |-> maxVBal[aa], maxVal |-> maxVal[aa],
                                  acc |-> aa]}
      BY <2>3 DEF Phase1b, Send
    <3>2. m1 \in msgs /\ m2 \in msgs  BY <3>1
    <3> QED  BY <3>2 DEF MsgInv
  <2>4. ASSUME NEW b \in Ballots, Phase2a(b)  PROVE m1 = m2
    <3>0. ~ \E mm \in msgs : (mm.type = "2a") /\ (mm.bal = b)  BY <2>4 DEF Phase2a
    <3>1. PICK v \in Values :
              msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
      BY <2>4 DEF Phase2a, Send
    <3>2. m1 \in msgs => m1.bal # b  BY <3>0
    <3>3. m2 \in msgs => m2.bal # b  BY <3>0
    <3>4. CASE m1 \in msgs /\ m2 \in msgs  BY <3>4 DEF MsgInv
    <3>5. CASE m1 \notin msgs
      <4>1. m1 = [type |-> "2a", bal |-> b, val |-> v]  BY <3>1, <3>5
      <4>2. m2.bal = b  BY <4>1
      <4>3. m2 \notin msgs  BY <4>2, <3>3
      <4>4. m2 = [type |-> "2a", bal |-> b, val |-> v]  BY <3>1, <4>3
      <4> QED  BY <4>1, <4>4
    <3>6. CASE m2 \notin msgs
      <4>1. m2 = [type |-> "2a", bal |-> b, val |-> v]  BY <3>1, <3>6
      <4>2. m1.bal = b  BY <4>1
      <4>3. m1 \notin msgs  BY <4>2, <3>2
      <4>4. m1 = [type |-> "2a", bal |-> b, val |-> v]  BY <3>1, <4>3
      <4> QED  BY <4>1, <4>4
    <3> QED  BY <3>4, <3>5, <3>6
  <2>5. ASSUME NEW aa \in Acceptors, Phase2b(aa)  PROVE m1 = m2
    <3>1. PICK mp \in msgs :
              msgs' = msgs \cup {[type |-> "2b", bal |-> mp.bal,
                                  val |-> mp.val, acc |-> aa]}
      BY <2>5 DEF Phase2b, Send
    <3>2. m1 \in msgs /\ m2 \in msgs  BY <3>1
    <3> QED  BY <3>2 DEF MsgInv
  <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
(* Every message already in msgs still satisfies its invariant.            *)
<1>OLD. ASSUME NEW mm \in msgs
        PROVE  /\ (mm.type = "1b") =>
                    /\ mm.bal =< maxBal'[mm.acc]
                    /\ \/ /\ mm.maxVal \in Values
                          /\ mm.maxVBal \in Ballots
                          /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
                       \/ /\ mm.maxVal = None
                          /\ mm.maxVBal = -1
                    /\ \A c \in (mm.maxVBal+1) .. (mm.bal-1) :
                          ~ \E v \in Values : VotedForIn(mm.acc, v, c)'
               /\ (mm.type = "2a") =>
                    /\ SafeAt(mm.val, mm.bal)'
                    /\ \A ma \in msgs' :
                          (ma.type = "2a") /\ (ma.bal = mm.bal) => (ma = mm)
               /\ (mm.type = "2b") =>
                    /\ \E ma \in msgs' : /\ ma.type = "2a"
                                         /\ ma.bal = mm.bal
                                         /\ ma.val = mm.val
                    /\ mm.bal =< maxVBal'[mm.acc]
  <2>1. (mm.type = "1b") =>
          /\ mm.bal =< maxBal'[mm.acc]
          /\ \/ /\ mm.maxVal \in Values
                /\ mm.maxVBal \in Ballots
                /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
             \/ /\ mm.maxVal = None
                /\ mm.maxVBal = -1
          /\ \A c \in (mm.maxVBal+1) .. (mm.bal-1) :
                ~ \E v \in Values : VotedForIn(mm.acc, v, c)'
    <3> SUFFICES ASSUME mm.type = "1b"
                 PROVE  /\ mm.bal =< maxBal'[mm.acc]
                        /\ \/ /\ mm.maxVal \in Values
                              /\ mm.maxVBal \in Ballots
                              /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
                           \/ /\ mm.maxVal = None
                              /\ mm.maxVBal = -1
                        /\ \A c \in (mm.maxVBal+1) .. (mm.bal-1) :
                              ~ \E v \in Values : VotedForIn(mm.acc, v, c)'
      OBVIOUS
    <3>acc. mm.acc \in Acceptors /\ mm.maxVBal \in Ballots \cup {-1}
      BY DEF TypeOK, Messages
    <3>0. /\ mm.bal =< maxBal[mm.acc]
          /\ \/ /\ mm.maxVal \in Values
                /\ mm.maxVBal \in Ballots
                /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
             \/ /\ mm.maxVal = None
                /\ mm.maxVBal = -1
          /\ \A c \in (mm.maxVBal+1) .. (mm.bal-1) :
                ~ \E v \in Values : VotedForIn(mm.acc, v, c)
      BY DEF MsgInv
    <3>1. mm.bal =< maxBal'[mm.acc]
      <4>1. maxBal[mm.acc] =< maxBal'[mm.acc]  BY MaxBalMonotone, <3>acc
      <4>2. maxBal[mm.acc] \in Ballots \cup {-1}  BY <3>acc DEF TypeOK
      <4>3. mm.bal \in Ballots  BY DEF TypeOK, Messages
      <4>4. maxBal'[mm.acc] \in Ballots \cup {-1}  BY <1>type, <3>acc DEF TypeOK
      <4> QED  BY <3>0, <4>1, <4>2, <4>3, <4>4
    <3>2. \/ /\ mm.maxVal \in Values
             /\ mm.maxVBal \in Ballots
             /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
          \/ /\ mm.maxVal = None
             /\ mm.maxVBal = -1
      <4>1. CASE /\ mm.maxVal \in Values
                 /\ mm.maxVBal \in Ballots
                 /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
        <5>1. VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)'
          BY <4>1, <3>acc, VotedForInStable
        <5> QED  BY <4>1, <5>1
      <4>2. CASE /\ mm.maxVal = None
                 /\ mm.maxVBal = -1
        BY <4>2
      <4> QED  BY <3>0, <4>1, <4>2
    <3>3. \A c \in (mm.maxVBal+1) .. (mm.bal-1) :
              ~ \E v \in Values : VotedForIn(mm.acc, v, c)'
      <4> SUFFICES ASSUME NEW c \in (mm.maxVBal+1) .. (mm.bal-1),
                          NEW v \in Values, VotedForIn(mm.acc, v, c)'
                   PROVE  FALSE
        OBVIOUS
      <4>1. ~ VotedForIn(mm.acc, v, c)  BY <3>0
      <4>2. c \in Ballots  BY <3>acc
      <4>3. c >= maxBal[mm.acc]  BY <4>1, <4>2, <3>acc, VoteCreation
      <4>4. mm.bal =< maxBal[mm.acc]  BY <3>0
      <4>5. mm.bal \in Ballots /\ maxBal[mm.acc] \in Ballots \cup {-1}
        BY <3>acc DEF TypeOK, Messages
      <4> QED  BY <4>3, <4>4, <4>5, <4>2
    <3> QED  BY <3>1, <3>2, <3>3
  <2>2. (mm.type = "2a") =>
          /\ SafeAt(mm.val, mm.bal)'
          /\ \A ma \in msgs' :
                (ma.type = "2a") /\ (ma.bal = mm.bal) => (ma = mm)
    <3> SUFFICES ASSUME mm.type = "2a"
                 PROVE  /\ SafeAt(mm.val, mm.bal)'
                        /\ \A ma \in msgs' :
                              (ma.type = "2a") /\ (ma.bal = mm.bal) => (ma = mm)
      OBVIOUS
    <3>val. mm.val \in Values /\ mm.bal \in Ballots  BY DEF TypeOK, Messages
    <3>1. SafeAt(mm.val, mm.bal)  BY DEF MsgInv
    <3>2. SafeAt(mm.val, mm.bal)'  BY <3>1, <3>val, SafeAtStable, <1>type
    <3>3. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = mm.bal) => (ma = mm)
      BY <1>uniq, <1>sub
    <3> QED  BY <3>2, <3>3
  <2>3. (mm.type = "2b") =>
          /\ \E ma \in msgs' : /\ ma.type = "2a"
                               /\ ma.bal = mm.bal
                               /\ ma.val = mm.val
          /\ mm.bal =< maxVBal'[mm.acc]
    <3> SUFFICES ASSUME mm.type = "2b"
                 PROVE  /\ \E ma \in msgs' : /\ ma.type = "2a"
                                             /\ ma.bal = mm.bal
                                             /\ ma.val = mm.val
                        /\ mm.bal =< maxVBal'[mm.acc]
      OBVIOUS
    <3>acc. mm.acc \in Acceptors  BY DEF TypeOK, Messages
    <3>1. \E ma \in msgs : /\ ma.type = "2a"
                           /\ ma.bal = mm.bal
                           /\ ma.val = mm.val
      BY DEF MsgInv
    <3>2. \E ma \in msgs' : /\ ma.type = "2a"
                            /\ ma.bal = mm.bal
                            /\ ma.val = mm.val
      BY <3>1, <1>sub
    <3>3. mm.bal =< maxVBal[mm.acc]  BY DEF MsgInv
    <3>4. mm.bal =< maxVBal'[mm.acc]
      <4>1. maxVBal[mm.acc] =< maxVBal'[mm.acc]  BY MaxVBalMonotone, <3>acc
      <4>2. maxVBal[mm.acc] \in Ballots \cup {-1}  BY <3>acc DEF TypeOK
      <4>3. mm.bal \in Ballots  BY DEF TypeOK, Messages
      <4>4. maxVBal'[mm.acc] \in Ballots \cup {-1}  BY <1>type, <3>acc DEF TypeOK
      <4> QED  BY <3>3, <4>1, <4>2, <4>3, <4>4
    <3> QED  BY <3>2, <3>4
  <2> QED  BY <2>1, <2>2, <2>3
(* Main goal: every message in msgs' satisfies the (primed) invariant.     *)
<1> SUFFICES ASSUME NEW m \in msgs'
             PROVE  /\ (m.type = "1b") =>
                          /\ m.bal =< maxBal'[m.acc]
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
                                               /\ ma.bal = m.bal
                                               /\ ma.val = m.val
                          /\ m.bal =< maxVBal'[m.acc]
  BY DEF MsgInv
<1>main. CASE m \in msgs
  BY <1>main, <1>OLD
<1>newm. CASE m \notin msgs
  <2>1. CASE vars' = vars
    BY <2>1, <1>newm DEF vars
  <2>2. CASE \E b \in Ballots : Phase1a(b)
    <3>b. PICK b \in Ballots : Phase1a(b)  BY <2>2
    <3>1. m = [type |-> "1a", bal |-> b]
      BY <3>b, <1>newm DEF Phase1a, Send
    <3>2. m.type = "1a"  BY <3>1
    <3> QED  BY <3>2
  <2>3. CASE \E b \in Ballots : Phase2a(b)
    <3>b. PICK b \in Ballots : Phase2a(b)  BY <2>3
    <3>0. PICK v \in Values :
              /\ \E Q \in Quorums :
                   \E S \in SUBSET {mx \in msgs : (mx.type = "1b") /\ (mx.bal = b)} :
                      /\ \A a \in Q : \E mx \in S : mx.acc = a
                      /\ \/ \A mx \in S : mx.maxVBal = -1
                         \/ \E c \in 0..(b-1) :
                               /\ \A mx \in S : mx.maxVBal =< c
                               /\ \E mx \in S : /\ mx.maxVBal = c
                                                /\ mx.maxVal = v
              /\ Send([type |-> "2a", bal |-> b, val |-> v])
      BY <3>b DEF Phase2a
    <3>1. m = [type |-> "2a", bal |-> b, val |-> v]
      BY <3>0, <1>newm DEF Send
    <3>2. m.type = "2a" /\ m.val = v /\ m.bal = b  BY <3>1
    <3>3. PICK Q \in Quorums :
              \E S \in SUBSET {mx \in msgs : (mx.type = "1b") /\ (mx.bal = b)} :
                 /\ \A a \in Q : \E mx \in S : mx.acc = a
                 /\ \/ \A mx \in S : mx.maxVBal = -1
                    \/ \E c \in 0..(b-1) :
                          /\ \A mx \in S : mx.maxVBal =< c
                          /\ \E mx \in S : /\ mx.maxVBal = c
                                           /\ mx.maxVal = v
      BY <3>0
    <3>4. PICK S \in SUBSET {mx \in msgs : (mx.type = "1b") /\ (mx.bal = b)} :
              /\ \A a \in Q : \E mx \in S : mx.acc = a
              /\ \/ \A mx \in S : mx.maxVBal = -1
                 \/ \E c \in 0..(b-1) :
                       /\ \A mx \in S : mx.maxVBal =< c
                       /\ \E mx \in S : /\ mx.maxVBal = c
                                        /\ mx.maxVal = v
      BY <3>3
    <3>5. SafeAt(v, b)  BY <3>4, ShowsSafeAt
    <3>6. SafeAt(v, b)'  BY <3>5, SafeAtStable, <1>type
    <3>7. SafeAt(m.val, m.bal)'  BY <3>6, <3>2
    <3>8. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
      BY <1>uniq, <3>2
    <3> QED  BY <3>2, <3>7, <3>8
  <2>4. CASE \E aa \in Acceptors : Phase1b(aa)
    <3>aa. PICK aa \in Acceptors : Phase1b(aa)  BY <2>4
    <3>0. PICK mp \in msgs :
              /\ mp.type = "1a"
              /\ mp.bal > maxBal[aa]
              /\ maxBal' = [maxBal EXCEPT ![aa] = mp.bal]
              /\ msgs' = msgs \cup {[type |-> "1b", bal |-> mp.bal,
                                     maxVBal |-> maxVBal[aa], maxVal |-> maxVal[aa],
                                     acc |-> aa]}
              /\ UNCHANGED <<maxVBal, maxVal>>
      BY <3>aa DEF Phase1b, Send
    <3>1. m = [type |-> "1b", bal |-> mp.bal, maxVBal |-> maxVBal[aa],
               maxVal |-> maxVal[aa], acc |-> aa]
      BY <3>0, <1>newm
    <3>2. /\ m.type = "1b" /\ m.bal = mp.bal /\ m.maxVBal = maxVBal[aa]
          /\ m.maxVal = maxVal[aa] /\ m.acc = aa
      BY <3>1
    <3>bal. mp.bal \in Ballots  BY <3>0 DEF TypeOK, Messages
    <3>vbal. maxVBal[aa] \in Ballots \cup {-1}  BY DEF TypeOK
    <3>3. m.bal =< maxBal'[m.acc]
      <4>1. maxBal'[aa] = mp.bal  BY <3>0 DEF TypeOK
      <4> QED  BY <4>1, <3>2, <3>bal
    <3>4. \/ /\ m.maxVal \in Values
             /\ m.maxVBal \in Ballots
             /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
          \/ /\ m.maxVal = None
             /\ m.maxVBal = -1
      <4>1. CASE maxVBal[aa] >= 0
        <5>1. maxVBal[aa] \in Ballots  BY <4>1, <3>vbal
        <5>2. maxVal[aa] \in Values  BY <4>1 DEF AccInv, TypeOK
        <5>3. VotedForIn(aa, maxVal[aa], maxVBal[aa])  BY <4>1 DEF AccInv
        <5>4. VotedForIn(m.acc, m.maxVal, m.maxVBal)'
          BY <5>3, <1>sub, <3>2 DEF VotedForIn
        <5> QED  BY <5>1, <5>2, <5>4, <3>2
      <4>2. CASE ~(maxVBal[aa] >= 0)
        <5>1. maxVBal[aa] = -1  BY <4>2, <3>vbal
        <5>2. maxVal[aa] = None  BY <5>1 DEF AccInv
        <5> QED  BY <5>1, <5>2, <3>2
      <4> QED  BY <4>1, <4>2
    <3>5. \A c \in (m.maxVBal+1) .. (m.bal-1) :
              ~ \E v \in Values : VotedForIn(m.acc, v, c)'
      <4> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1),
                          NEW v \in Values, VotedForIn(m.acc, v, c)'
                   PROVE  FALSE
        OBVIOUS
      <4>1. maxVBal'[aa] = maxVBal[aa]  BY <3>0 DEF TypeOK
      <4>2. c \in Ballots  BY <3>2, <3>vbal
      <4>3. c > maxVBal'[aa]  BY <3>2, <4>1, <3>vbal
      <4>4. ~ \E vv \in Values : VotedForIn(aa, vv, c)'
        BY <1>accP, <4>2, <4>3 DEF AccInv
      <4> QED  BY <4>4, <3>2
    <3> QED  BY <3>2, <3>3, <3>4, <3>5
  <2>5. CASE \E aa \in Acceptors : Phase2b(aa)
    <3>aa. PICK aa \in Acceptors : Phase2b(aa)  BY <2>5
    <3>0. PICK mp \in msgs :
              /\ mp.type = "2a"
              /\ mp.bal >= maxBal[aa]
              /\ maxVBal' = [maxVBal EXCEPT ![aa] = mp.bal]
              /\ msgs' = msgs \cup {[type |-> "2b", bal |-> mp.bal,
                                     val |-> mp.val, acc |-> aa]}
      BY <3>aa DEF Phase2b, Send
    <3>1. m = [type |-> "2b", bal |-> mp.bal, val |-> mp.val, acc |-> aa]
      BY <3>0, <1>newm
    <3>2. m.type = "2b" /\ m.bal = mp.bal /\ m.val = mp.val /\ m.acc = aa  BY <3>1
    <3>3. \E ma \in msgs' : /\ ma.type = "2a"
                            /\ ma.bal = m.bal
                            /\ ma.val = m.val
      <4>1. mp \in msgs'  BY <3>0, <1>sub
      <4> QED  BY <4>1, <3>0, <3>2
    <3>4. m.bal =< maxVBal'[m.acc]
      <4>1. maxVBal'[aa] = mp.bal  BY <3>0 DEF TypeOK
      <4>2. mp.bal \in Ballots  BY <3>0 DEF TypeOK, Messages
      <4> QED  BY <4>1, <4>2, <3>2
    <3> QED  BY <3>2, <3>3, <3>4
  <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1> QED  BY <1>main, <1>newm


(***************************************************************************)
(* Inv is an inductive invariant of the specification.                     *)
(***************************************************************************)
THEOREM Invariant == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, MsgInv, AccInv, VotedForIn, Messages, Ballots
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <2>1. TypeOK'  BY TypeOKInvariant DEF Inv
  <2>2. MsgInv'  BY MsgInvInvariant
  <2>3. AccInv'  BY AccInvInvariant
  <2> QED  BY <2>1, <2>2, <2>3 DEF Inv
<1> QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* If two values are chosen in ballots b1 =< b2, they are equal.           *)
(***************************************************************************)
LEMMA ChosenSafe ==
  ASSUME TypeOK, MsgInv, AccInv,
         NEW v1 \in Values, NEW v2 \in Values,
         NEW b1 \in Ballots, NEW b2 \in Ballots,
         b1 =< b2, ChosenIn(v1, b1), ChosenIn(v2, b2)
  PROVE  v1 = v2
<1> USE DEF Ballots
<1>1. SafeAt(v2, b2)
  <2>1. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)  BY DEF ChosenIn
  <2>2. Q2 # {}  BY QuorumAssumption, <2>1
  <2>3. PICK a \in Q2 : VotedForIn(a, v2, b2)  BY <2>1, <2>2
  <2>4. a \in Acceptors  BY <2>1, <2>3, QuorumAssumption
  <2> QED  BY <2>3, <2>4, VotedInv
<1>2. CASE b1 = b2
  <2>1. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)  BY DEF ChosenIn
  <2>2. PICK Q2 \in Quorums : \A a \in Q2 : VotedForIn(a, v2, b2)  BY DEF ChosenIn
  <2>3. Q1 \cap Q2 # {}  BY QuorumAssumption, <2>1, <2>2
  <2>4. PICK a \in Q1 \cap Q2 : TRUE  BY <2>3
  <2>5. VotedForIn(a, v1, b1) /\ VotedForIn(a, v2, b1)
    BY <2>1, <2>2, <2>4, <1>2
  <2>6. a \in Acceptors  BY <2>1, <2>4, QuorumAssumption
  <2> QED  BY <2>5, <2>6, VotedOnce
<1>3. CASE b1 < b2
  <2>1. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)  BY DEF ChosenIn
  <2>2. b1 \in 0..(b2-1)  BY <1>3
  <2>3. PICK Q \in Quorums : \A a \in Q : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
    BY <1>1, <2>2 DEF SafeAt
  <2>4. Q1 \cap Q # {}  BY QuorumAssumption, <2>1, <2>3
  <2>5. PICK a \in Q1 \cap Q : TRUE  BY <2>4
  <2>6. a \in Acceptors  BY <2>1, <2>5, QuorumAssumption
  <2>7. VotedForIn(a, v1, b1)  BY <2>1, <2>5
  <2>8. VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)  BY <2>3, <2>5
  <2>9. ~ WontVoteIn(a, b1)  BY <2>7 DEF WontVoteIn
  <2>10. VotedForIn(a, v2, b1)  BY <2>8, <2>9
  <2> QED  BY <2>7, <2>10, <2>6, VotedOnce
<1> QED  BY <1>2, <1>3

THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballots
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv, NEW v1 \in Values, NEW v2 \in Values,
                      Chosen(v1), Chosen(v2)
               PROVE  v1 = v2
    BY DEF Consistency
  <2>1. PICK b1 \in Ballots : ChosenIn(v1, b1)  BY DEF Chosen
  <2>2. PICK b2 \in Ballots : ChosenIn(v2, b2)  BY DEF Chosen
  <2>3. CASE b1 =< b2
    BY <2>1, <2>2, <2>3, ChosenSafe DEF Inv
  <2>4. CASE b2 =< b1
    BY <2>1, <2>2, <2>4, ChosenSafe DEF Inv
  <2> QED  BY <2>3, <2>4
<1>2. Spec => []Inv  BY Invariant
<1> QED  BY <1>1, <1>2, PTL

-----------------------------------------------------------------------------
chosenBar == {v \in Values : Chosen(v)}

C == INSTANCE Consensus WITH chosen <- chosenBar

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