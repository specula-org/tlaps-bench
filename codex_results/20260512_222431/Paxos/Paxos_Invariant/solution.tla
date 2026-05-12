------------------------------- MODULE Paxos_Invariant -------------------------------
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

LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
  PROOF OMITTED

Ballots == Nat

None == CHOOSE v : v \notin Values

LEMMA NoneNotAValue == None \notin Values
  PROOF OMITTED

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
LEMMA VotedInv ==
        MsgInv /\ TypeOK => 
            \A a \in Acceptors, v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => SafeAt(v, b) /\ b =< maxVBal[a]
  PROOF OMITTED

LEMMA VotedOnce == \* OneValuePerBallot in Voting (TODO: Where/How/Why is it used?)
        MsgInv =>  \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
                       VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
  PROOF OMITTED

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
LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' => 
                          \A v \in Values, b \in Ballots:
                                  SafeAt(v, b) => SafeAt(v, b)'
  PROOF OMITTED

THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots
<1>1. Init => Inv
  BY Isa DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn
  
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. Inv /\ Next => Inv'
    <3> SUFFICES ASSUME Inv, Next
                 PROVE  Inv'
      OBVIOUS
  <3> USE DEF Inv
  <3>1. TypeOK'
    <4>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE TypeOK'
      BY <4>1 DEF TypeOK, Phase1a, Send, Messages
    <4>2. ASSUME NEW b \in Ballots, Phase2a(b) PROVE TypeOK'
      <5>1. PICK v \in Values :
               /\ Send([type |-> "2a", bal |-> b, val |-> v])
               /\ UNCHANGED <<maxBal, maxVBal, maxVal>>
        BY <4>2, Zenon DEF Phase2a
      <5>. QED
        BY <5>1 DEF TypeOK, Send, Messages
    <4>3. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE TypeOK'
      <5>. PICK m \in msgs : Phase1b(a)!(m)
        BY <4>3, Zenon DEF Phase1b
      <5>. QED  BY DEF Send, TypeOK, Messages
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE TypeOK'
      <5>. PICK m \in msgs : Phase2b(a)!(m)
        BY <4>4, Zenon DEF Phase2b
      <5>. QED  BY DEF Send, TypeOK, Messages
    <4>. QED  BY <4>1, <4>2, <4>3, <4>4 DEF Next
  <3>2. AccInv'
    <4>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE AccInv'
      BY <3>1, <4>1, SafeAtStable DEF AccInv, TypeOK, Phase1a, VotedForIn, Send
    <4>2. ASSUME NEW b \in Ballots, Phase2a(b) PROVE AccInv'
        BY <3>1, <4>2, SafeAtStable DEF AccInv, TypeOK, Phase2a, VotedForIn, Send
    <4>3. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE AccInv'
        BY <3>1, <4>3, SafeAtStable DEF AccInv, TypeOK, Phase1b, VotedForIn, Send
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE AccInv'
      <5>1. PICK m \in msgs : Phase2b(a)!(m)
        BY <4>4, Zenon DEF Phase2b
      <5>2. \A acc \in Acceptors : 
               /\ maxVal'[acc] = None <=> maxVBal'[acc] = -1
               /\ maxVBal'[acc] =< maxBal'[acc]
        BY <3>1, <5>1, NoneNotAValue DEF AccInv, TypeOK, Messages
      <5>3. \A aa,vv,bb : VotedForIn(aa,vv,bb)' <=>
                          VotedForIn(aa,vv,bb) \/ (aa = a /\ vv = maxVal'[a] /\ bb = maxVBal'[a])
        BY <5>1, Isa DEF VotedForIn, Send, TypeOK, Messages
      <5>4. ASSUME NEW acc \in Acceptors, maxVBal'[acc] >= 0
            PROVE  VotedForIn(acc, maxVal[acc], maxVBal[acc])'
        BY <5>1, <5>3, <5>4 DEF AccInv, TypeOK
      <5>5. ASSUME NEW acc \in Acceptors, NEW c \in Ballots, c > maxVBal'[acc],
                   NEW v \in Values, VotedForIn(acc, v, c)'
            PROVE  FALSE
        BY <5>1, <5>3, <5>5, <3>1 DEF AccInv, TypeOK
      <5>. QED  BY <5>2, <5>4, <5>5 DEF AccInv
    <4>. QED  BY <4>1, <4>2, <4>3, <4>4 DEF Next
  <3>3. MsgInv'
    <4>1. ASSUME NEW b \in Ballots, Phase1a(b)
          PROVE  MsgInv'
      <5>1. \A aa,vv,bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY <4>1 DEF Phase1a, Send, VotedForIn
      <5>. QED
        BY <4>1, <5>1, SafeAtStable, <3>1 DEF Phase1a, MsgInv, TypeOK, Messages, Send
    <4>2. ASSUME NEW a \in Acceptors, Phase1b(a)
          PROVE  MsgInv'
      <5>. PICK m \in msgs : Phase1b(a)!(m)
        BY <4>2, Zenon DEF Phase1b
      <5>1. \A aa,vv,bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY DEF Send, VotedForIn
      <5>. DEFINE mm == [type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a], 
                         maxVal |-> maxVal[a], acc |-> a]
      <5>2. mm.bal =< maxBal'[mm.acc]
        BY DEF TypeOK, Messages
      <5>3. \/ /\ mm.maxVal \in Values
               /\ mm.maxVBal \in Ballots
               /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
            \/ /\ mm.maxVal = None
               /\ mm.maxVBal = -1
        BY DEF TypeOK, AccInv
      <5>4. \A c \in (mm.maxVBal+1) .. (mm.bal-1) :
                ~ \E v \in Values : VotedForIn(mm.acc, v, c)
        BY DEF AccInv, TypeOK, Messages
      <5>. QED
        BY <5>1, <5>2, <5>3, <5>4, SafeAtStable DEF MsgInv, TypeOK, Messages, Send
    <4>3. ASSUME NEW b \in Ballots, Phase2a(b)
          PROVE  MsgInv'
      <5>1. ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
        BY <4>3, Zenon DEF Phase2a
      <5>1a. UNCHANGED <<maxBal, maxVBal, maxVal>>
        BY <4>3 DEF Phase2a
      <5>2. PICK v \in Values :
               /\ \E Q \in Quorums : 
                     \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
                        /\ \A a \in Q : \E m \in S : m.acc = a
                        /\ \/ \A m \in S : m.maxVBal = -1
                           \/ \E c \in 0..(b-1) : 
                                 /\ \A m \in S : m.maxVBal =< c
                                 /\ \E m \in S : /\ m.maxVBal = c
                                                 /\ m.maxVal = v
               /\ Send([type |-> "2a", bal |-> b, val |-> v])
        BY <4>3 DEF Phase2a
      <5>. DEFINE mm == [type |-> "2a", bal |-> b, val |-> v]
      <5>3. msgs' = msgs \cup {mm}
        BY <5>2 DEF Send
      <5>4. \A aa, vv, bb : VotedForIn(aa,vv,bb)' <=> VotedForIn(aa,vv,bb)
        BY <5>3 DEF VotedForIn
      <5>6. \A m,ma \in msgs' : m.type = "2a" /\ ma.type = "2a" /\ ma.bal = m.bal
                                => ma = m
        BY <5>1, <5>3, Isa DEF MsgInv
      <5>10. SafeAt(v,b)
        <6>0. PICK Q \in Quorums, 
                   S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
                     /\ \A a \in Q : \E m \in S : m.acc = a
                     /\ \/ \A m \in S : m.maxVBal = -1
                        \/ \E c \in 0..(b-1) : 
                              /\ \A m \in S : m.maxVBal =< c
                              /\ \E m \in S : /\ m.maxVBal = c
                                              /\ m.maxVal = v
          BY <5>2, Zenon
        <6>1. CASE \A m \in S : m.maxVBal = -1
          \* In that case, no acceptor in Q voted in any ballot less than b,
          \* by the last conjunct of MsgInv for type "1b" messages, and that's enough
          BY <6>1, <6>0 DEF TypeOK, MsgInv, SafeAt, WontVoteIn, Messages
        <6>2. ASSUME NEW c \in 0 .. (b-1),
                     \A m \in S : m.maxVBal =< c,
                     NEW ma \in S, ma.maxVBal = c, ma.maxVal = v
              PROVE  SafeAt(v,b)
          <7>. SUFFICES ASSUME NEW d \in 0 .. (b-1)
                        PROVE  \E QQ \in Quorums : \A q \in QQ : 
                                  VotedForIn(q,v,d) \/ WontVoteIn(q,d)
            BY Zenon DEF SafeAt
          <7>1. CASE d \in 0 .. (c-1)
            \* The "1b" message for v with maxVBal value c must have been safe
            \* according to MsgInv for "1b" messages and lemma VotedInv, 
            \* and that proves the assertion
            BY <6>2, <7>1, VotedInv DEF SafeAt, MsgInv, TypeOK, Messages
          <7>2. CASE d = c
            <8>1. VotedForIn(ma.acc, v, c)
              BY <6>2 DEF MsgInv
            <8>2. \A q \in Q, w \in Values : VotedForIn(q, w, c) => w = v
              BY <8>1, VotedOnce, QuorumAssumption DEF TypeOK, Messages
            <8>3. \A q \in Q : maxBal[q] > c
              BY <6>0 DEF MsgInv, TypeOK, Messages
            <8>. QED
              BY <7>2, <8>2, <8>3 DEF WontVoteIn
          <7>3. CASE d \in (c+1) .. (b-1)
            \* By the last conjunct of MsgInv for type "1b" messages, no acceptor in Q
            \* voted at any of these ballots.
            BY <7>3, <6>0, <6>2 DEF MsgInv, TypeOK, Messages, WontVoteIn
          <7>. QED  BY <7>1, <7>2, <7>3
        <6>. QED  BY <6>0, <6>1, <6>2
      <5>11. SafeAt(mm.val,mm.bal)'
        BY <5>10, <3>1, SafeAtStable
      <5>. QED
         BY <3>1, <5>1a, <5>3, <5>4, <5>6, <5>11, SafeAtStable, Zenon
           DEF MsgInv, TypeOK, Messages
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a)
          PROVE  MsgInv'
      <5>. PICK m \in msgs : Phase2b(a)!(m)
        BY <4>4, Zenon DEF Phase2b
      <5>1. \A aa, vv, bb : VotedForIn(aa,vv,bb) => VotedForIn(aa,vv,bb)'
        BY DEF VotedForIn, Send
      <5>2. \A mm \in msgs : mm.type = "1b"
               => \A v \in Values, c \in (mm.maxVBal+1) .. (mm.bal-1) :
                     ~ VotedForIn(mm.acc, v, c) => ~ VotedForIn(mm.acc, v, c)'
        BY DEF Send, VotedForIn, MsgInv, TypeOK, Messages
      <5>. QED
        BY <5>1, <5>2, SafeAtStable, <3>1 DEF MsgInv, Send, TypeOK, Messages
    <4>. QED  BY <4>1, <4>2, <4>3, <4>4 DEF Next
  <3>. QED  BY <3>1, <3>2, <3>3 DEF Inv
  <2>2. Inv /\ UNCHANGED vars => Inv'
    <3> SUFFICES ASSUME Inv, UNCHANGED vars
                 PROVE  Inv'
      OBVIOUS
    <3>. QED
      BY DEF Inv, vars, TypeOK, MsgInv, AccInv, VotedForIn, SafeAt, WontVoteIn
  <2>3. QED
    BY <2>1, <2>2 DEF vars

<1>. QED  BY <1>1, <1>2, PTL DEF Spec

=============================================================================
