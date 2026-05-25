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

(***************************************************************************)
(* Helper lemmas for the inductive invariant proof.                        *)
(***************************************************************************)

LEMMA NoneNotInValues == None \notin Values
<1>1. \E v : v \notin Values
  <2> SUFFICES ASSUME \A v : v \in Values
               PROVE  FALSE
    OBVIOUS
  <2> DEFINE R == {x \in Values : x \notin x}
  <2>1. R \in Values
    OBVIOUS
  <2>2. R \in R <=> R \notin R
    BY <2>1
  <2>3. QED
    BY <2>2
<1>2. QED
  BY <1>1 DEF None

(* Characterization of how VotedForIn changes when a single message is      *)
(* added to msgs.                                                           *)
LEMMA VotedForIn_Send ==
  ASSUME NEW mm, NEW aa, NEW vv, NEW bb, msgs' = msgs \cup {mm}
  PROVE  VotedForIn(aa, vv, bb)' <=>
            (VotedForIn(aa, vv, bb)
              \/ (mm.type = "2b" /\ mm.val = vv /\ mm.bal = bb /\ mm.acc = aa))
BY DEF VotedForIn

(* The set of messages only grows under Next. *)
LEMMA MsgsGrow == Next => msgs \subseteq msgs'
BY DEF Next, Phase1a, Phase1b, Phase2a, Phase2b, Send

(* VotedForIn is monotone: a vote, once cast, stays cast. *)
LEMMA VotedForInMonotone ==
  ASSUME Next, NEW aa, NEW vv, NEW bb, VotedForIn(aa, vv, bb)
  PROVE  VotedForIn(aa, vv, bb)'
BY MsgsGrow DEF VotedForIn

(* maxBal is non-decreasing under Next. *)
LEMMA MaxBalMonotone ==
  ASSUME TypeOK, Next, NEW a \in Acceptors
  PROVE  maxBal[a] =< maxBal'[a]
<1> USE DEF Ballots, TypeOK
<1>1. CASE \E b \in Ballots : Phase1a(b)
  BY <1>1 DEF Phase1a
<1>2. CASE \E b \in Ballots : Phase2a(b)
  BY <1>2 DEF Phase2a
<1>3. CASE \E aa \in Acceptors : Phase1b(aa)
  <2> PICK aa \in Acceptors : Phase1b(aa)  BY <1>3
  <2> PICK m \in msgs : /\ m.bal > maxBal[aa]
                       /\ maxBal' = [maxBal EXCEPT ![aa] = m.bal]
    BY DEF Phase1b
  <2> QED  BY Z3
<1>4. CASE \E aa \in Acceptors : Phase2b(aa)
  <2> PICK aa \in Acceptors : Phase2b(aa)  BY <1>4
  <2> PICK m \in msgs : /\ m.bal >= maxBal[aa]
                       /\ maxBal' = [maxBal EXCEPT ![aa] = m.bal]
    BY DEF Phase2b
  <2> QED  BY Z3
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(* At any given ballot, all votes are for the same value. *)
LEMMA VotedOnce ==
  MsgInv => \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
                 VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
BY DEF MsgInv, VotedForIn

(* A newly cast vote (one not present before) must be at a ballot at least  *)
(* as high as the voter's current maxBal.                                   *)
LEMMA NewVoteBallot ==
  ASSUME TypeOK, Next,
         NEW a \in Acceptors, NEW v \in Values, NEW b \in Ballots,
         VotedForIn(a, v, b)', ~VotedForIn(a, v, b)
  PROVE  maxBal[a] =< b
<1> USE DEF Ballots, TypeOK
<1>1. CASE \E bb \in Ballots : Phase1a(bb)
  <2> PICK bb \in Ballots : Phase1a(bb)  BY <1>1
  <2> msgs' = msgs \cup {[type |-> "1a", bal |-> bb]}  BY DEF Phase1a, Send
  <2> QED  BY VotedForIn_Send
<1>2. CASE \E bb \in Ballots : Phase2a(bb)
  <2> PICK bb \in Ballots : Phase2a(bb)  BY <1>2
  <2> PICK vv \in Values : msgs' = msgs \cup {[type |-> "2a", bal |-> bb, val |-> vv]}
    BY DEF Phase2a, Send
  <2> QED  BY VotedForIn_Send
<1>3. CASE \E aa \in Acceptors : Phase1b(aa)
  <2> PICK aa \in Acceptors : Phase1b(aa)  BY <1>3
  <2> PICK m \in msgs :
        msgs' = msgs \cup {[type |-> "1b", bal |-> m.bal,
              maxVBal |-> maxVBal[aa], maxVal |-> maxVal[aa], acc |-> aa]}
    BY DEF Phase1b, Send
  <2> QED  BY VotedForIn_Send
<1>4. CASE \E aa \in Acceptors : Phase2b(aa)
  <2> PICK aa \in Acceptors : Phase2b(aa)  BY <1>4
  <2> PICK m \in msgs :
        /\ m.bal >= maxBal[aa]
        /\ msgs' = msgs \cup {[type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> aa]}
    BY DEF Phase2b, Send
  <2>1. m.bal = b /\ aa = a
    BY VotedForIn_Send
  <2> QED  BY <2>1
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(* SafeAt(v,b) is stable: once true it remains true throughout execution.   *)
LEMMA SafeAtStable ==
  ASSUME Inv, Next, TypeOK',
         NEW v \in Values, NEW b \in Ballots, SafeAt(v, b)
  PROVE  SafeAt(v, b)'
<1> USE DEF Ballots, Inv, TypeOK
<1> SUFFICES ASSUME NEW c \in 0..(b-1)
             PROVE  \E Q \in Quorums :
                      \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
  BY DEF SafeAt
<1>c. c \in Ballots
  OBVIOUS
<1>1. PICK Q \in Quorums :
            \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
  BY DEF SafeAt
<1>2. \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
  <2> SUFFICES ASSUME NEW a \in Q
               PROVE  VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
    OBVIOUS
  <2>0. a \in Acceptors
    BY QuorumAssumption
  <2>1. VotedForIn(a, v, c) \/ WontVoteIn(a, c)
    BY <1>1
  <2>2. CASE VotedForIn(a, v, c)
    BY <2>2, VotedForInMonotone
  <2>3. CASE WontVoteIn(a, c)
    <3>t. maxBal[a] \in Int /\ maxBal'[a] \in Int /\ c \in Int
      BY <2>0, <1>c, TypeOK'
    <3>1. maxBal[a] > c
      BY <2>3 DEF WontVoteIn
    <3>2. maxBal[a] =< maxBal'[a]
      BY MaxBalMonotone, <2>0
    <3>3. maxBal'[a] > c
      BY <3>1, <3>2, <3>t
    <3>4. \A vv \in Values : ~ VotedForIn(a, vv, c)'
      <4> SUFFICES ASSUME NEW vv \in Values, VotedForIn(a, vv, c)'
                   PROVE  FALSE
        OBVIOUS
      <4>1. ~ VotedForIn(a, vv, c)
        BY <2>3 DEF WontVoteIn
      <4>2. maxBal[a] =< c
        BY NewVoteBallot, <4>1, <2>0, <1>c
      <4>3. QED
        BY <3>1, <4>2, <3>t
    <3>5. QED
      BY <3>3, <3>4 DEF WontVoteIn
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>3. QED
  BY <1>2

(* A cast vote is for a value that is safe at that ballot. *)
LEMMA VotedInv ==
  ASSUME MsgInv, TypeOK,
         NEW a \in Acceptors, NEW v \in Values, NEW b \in Ballots,
         VotedForIn(a, v, b)
  PROVE  SafeAt(v, b)
<1>1. PICK mb \in msgs : mb.type = "2b" /\ mb.val = v /\ mb.bal = b /\ mb.acc = a
  BY DEF VotedForIn
<1>2. PICK ma \in msgs : ma.type = "2a" /\ ma.bal = b /\ ma.val = v
  BY <1>1 DEF MsgInv
<1>3. SafeAt(ma.val, ma.bal)
  BY <1>2 DEF MsgInv
<1> QED
  BY <1>2, <1>3

(***************************************************************************)
(* The inductive step, one lemma per action.                              *)
(***************************************************************************)

LEMMA Phase1a_Inv ==
  ASSUME Inv, NEW b \in Ballots, Phase1a(b)
  PROVE  Inv'
<1> USE DEF Ballots, Inv
<1> DEFINE m0 == [type |-> "1a", bal |-> b]
<1>n. Next
  BY DEF Next
<1>s. /\ msgs' = msgs \cup {m0}
      /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
  BY DEF Phase1a, Send
<1>v. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
  BY <1>s, VotedForIn_Send
<1>1. TypeOK'
  BY <1>s DEF TypeOK, Messages
<1>2. MsgInv'
  <2> SUFFICES ASSUME NEW m \in msgs'
               PROVE  /\ (m.type = "1b") =>
                          /\ m.bal =< maxBal'[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
                          /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
                      /\ (m.type = "2a") =>
                          /\ SafeAt(m.val, m.bal)'
                          /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                      /\ (m.type = "2b") =>
                          /\ \E ma \in msgs' : /\ ma.type = "2a"
                                               /\ ma.bal  = m.bal
                                               /\ ma.val  = m.val
                          /\ m.bal =< maxVBal'[m.acc]
    BY DEF MsgInv
  <2>m. m \in msgs \/ m = m0
    BY <1>s
  <2>1. CASE m \in msgs
    <3>1. (m.type = "1b") =>
              /\ m.bal =< maxBal'[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
      BY <2>1, <1>s, <1>v DEF MsgInv
    <3>2. (m.type = "2a") =>
              /\ SafeAt(m.val, m.bal)'
              /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
      <4> SUFFICES ASSUME m.type = "2a"
                   PROVE  /\ SafeAt(m.val, m.bal)'
                          /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        OBVIOUS
      <4>1. m.val \in Values /\ m.bal \in Ballots
        BY <2>1 DEF TypeOK, Messages
      <4>2. SafeAt(m.val, m.bal)
        BY <2>1 DEF MsgInv
      <4>3. SafeAt(m.val, m.bal)'
        BY <4>1, <4>2, SafeAtStable, <1>n, <1>1
      <4>4. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        BY <2>1, <1>s DEF MsgInv
      <4> QED  BY <4>3, <4>4
    <3>3. (m.type = "2b") =>
              /\ \E ma \in msgs' : /\ ma.type = "2a"
                                   /\ ma.bal  = m.bal
                                   /\ ma.val  = m.val
              /\ m.bal =< maxVBal'[m.acc]
      BY <2>1, <1>s DEF MsgInv
    <3> QED  BY <3>1, <3>2, <3>3
  <2>2. CASE m = m0
    BY <2>2
  <2>3. QED
    BY <2>1, <2>2, <2>m
<1>3. AccInv'
  BY <1>s, <1>v DEF AccInv
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA Phase2a_Inv ==
  ASSUME Inv, NEW b \in Ballots, Phase2a(b)
  PROVE  Inv'
<1> USE DEF Ballots, Inv
<1>n. Next
  BY DEF Next
<1> PICK v \in Values, Q \in Quorums,
         S \in SUBSET {ms \in msgs : (ms.type = "1b") /\ (ms.bal = b)} :
         /\ \A a \in Q : \E mm \in S : mm.acc = a
         /\ \/ \A mm \in S : mm.maxVBal = -1
            \/ \E c \in 0..(b-1) :
                  /\ \A mm \in S : mm.maxVBal =< c
                  /\ \E mm \in S : mm.maxVBal = c /\ mm.maxVal = v
         /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
  BY DEF Phase2a, Send
<1> DEFINE m0 == [type |-> "2a", bal |-> b, val |-> v]
<1>s. /\ msgs' = msgs \cup {m0}
      /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
  BY DEF Phase2a, Send
<1>no2a. ~ \E mm \in msgs : (mm.type = "2a") /\ (mm.bal = b)
  BY DEF Phase2a
<1>v. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
  BY <1>s, VotedForIn_Send
<1>cov. \A a \in Q : \E mm \in S : mm.acc = a
  OBVIOUS
<1>Smsgs. \A mm \in S : mm \in msgs /\ mm.type = "1b" /\ mm.bal = b /\ mm.acc \in Acceptors
  BY DEF TypeOK, Messages
<1>1b. \A mm \in S :
         /\ mm.bal =< maxBal[mm.acc]
         /\ \/ /\ mm.maxVal \in Values
               /\ mm.maxVBal \in Ballots
               /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
            \/ /\ mm.maxVal = None
               /\ mm.maxVBal = -1
         /\ \A c \in (mm.maxVBal+1) .. (mm.bal-1) :
               ~ \E vv \in Values : VotedForIn(mm.acc, vv, c)
  BY <1>Smsgs, MsgInv DEF MsgInv
<1>Sint. \A mm \in S : mm.maxVBal \in Int
  BY <1>Smsgs DEF TypeOK, Messages
<1>safe. SafeAt(v, b)
  <2> SUFFICES ASSUME NEW c \in 0..(b-1)
               PROVE  \E QQ \in Quorums :
                        \A a \in QQ : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
    BY DEF SafeAt
  <2>cb. c \in Int /\ 0 =< c /\ c =< b - 1
    OBVIOUS
  <2>A. CASE \A mm \in S : mm.maxVBal = -1
    <3> WITNESS Q \in Quorums
    <3> TAKE a \in Q
    <3>1. a \in Acceptors
      BY QuorumAssumption
    <3>2. PICK mm \in S : mm.acc = a
      BY <1>cov, <3>1
    <3>3. mm \in msgs /\ mm.type = "1b" /\ mm.bal = b
      BY <1>Smsgs, <3>2
    <3>4. mm.maxVBal = -1
      BY <2>A, <3>2
    <3>5. /\ mm.bal =< maxBal[mm.acc]
          /\ \A cc \in (mm.maxVBal+1) .. (mm.bal-1) :
                ~ \E vv \in Values : VotedForIn(mm.acc, vv, cc)
      BY <1>1b, <3>2
    <3>ma. maxBal[a] \in Int
      BY <3>1 DEF TypeOK
    <3>6. maxBal[a] >= b
      BY <3>5, <3>3, <3>2, <3>ma
    <3>7. c \in (mm.maxVBal+1) .. (mm.bal-1)
      BY <3>4, <3>3, <2>cb
    <3>8. ~ \E vv \in Values : VotedForIn(a, vv, c)
      BY <3>5, <3>7, <3>2
    <3>9. WontVoteIn(a, c)
      BY <3>6, <3>8, <2>cb, <3>ma DEF WontVoteIn
    <3> QED
      BY <3>9
  <2>B. CASE \E c \in 0..(b-1) :
              /\ \A mm \in S : mm.maxVBal =< c
              /\ \E mm \in S : mm.maxVBal = c /\ mm.maxVal = v
    <3> PICK c1 \in 0..(b-1), mw \in S :
              /\ \A mm \in S : mm.maxVBal =< c1
              /\ mw.maxVBal = c1 /\ mw.maxVal = v
      BY <2>B
    <3>c1. c1 \in Int /\ 0 =< c1 /\ c1 =< b - 1
      OBVIOUS
    <3>maxle. \A mm \in S : mm.maxVBal =< c1
      OBVIOUS
    <3>mw. mw \in S /\ mw.maxVBal = c1 /\ mw.maxVal = v
      OBVIOUS
    <3>mwm. mw \in msgs /\ mw.type = "1b" /\ mw.bal = b /\ mw.acc \in Acceptors
      BY <1>Smsgs, <3>mw
    <3>mwv. VotedForIn(mw.acc, v, c1)
      BY <1>1b, <3>mw, <3>c1, <3>mwm
    <3>cc. CASE c < c1
      <4>1. SafeAt(v, c1)
        BY <3>mwm, <3>mwv, <3>c1, VotedInv
      <4>2. c \in 0..(c1 - 1)
        BY <2>cb, <3>cc, <3>c1
      <4> QED
        BY <4>1, <4>2 DEF SafeAt
    <3>dd. CASE c = c1
      <4> WITNESS Q \in Quorums
      <4> TAKE a \in Q
      <4>1. a \in Acceptors
        BY QuorumAssumption
      <4>2. PICK mm \in S : mm.acc = a
        BY <1>cov, <4>1
      <4>3. mm \in msgs /\ mm.type = "1b" /\ mm.bal = b /\ mm.acc \in Acceptors
        BY <1>Smsgs, <4>2
      <4>4. mm.maxVBal =< c1
        BY <3>maxle, <4>2
      <4>5. /\ mm.bal =< maxBal[mm.acc]
            /\ \/ /\ mm.maxVal \in Values
                  /\ mm.maxVBal \in Ballots
                  /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
               \/ /\ mm.maxVal = None
                  /\ mm.maxVBal = -1
            /\ \A cc \in (mm.maxVBal+1) .. (mm.bal-1) :
                  ~ \E vv \in Values : VotedForIn(mm.acc, vv, cc)
        BY <1>1b, <4>2
      <4>ma. maxBal[a] \in Int
        BY <4>1 DEF TypeOK
      <4>mvb. mm.maxVBal \in Int
        BY <1>Sint, <4>2
      <4>6. maxBal[a] >= b
        BY <4>5, <4>3, <4>2, <4>ma
      <4>cv. CASE mm.maxVBal = c1
        <5>1. mm.maxVal \in Values /\ VotedForIn(mm.acc, mm.maxVal, mm.maxVBal)
          BY <4>5, <4>cv, <3>c1
        <5>2. VotedForIn(a, mm.maxVal, c1)
          BY <5>1, <4>cv, <4>2
        <5>3. mm.maxVal = v
          BY VotedOnce, MsgInv, <5>1, <5>2, <3>mwv, <4>2, <4>3, <3>mwm, <3>c1
        <5> QED
          BY <5>2, <5>3, <3>dd
      <4>lt. CASE mm.maxVBal < c1
        <5>1. c1 \in (mm.maxVBal+1) .. (mm.bal-1)
          BY <4>lt, <4>3, <3>c1, <2>cb, <4>mvb
        <5>2. ~ \E vv \in Values : VotedForIn(a, vv, c1)
          BY <4>5, <5>1, <4>2
        <5>3. WontVoteIn(a, c1)
          BY <4>6, <5>2, <3>c1, <4>ma DEF WontVoteIn
        <5> QED
          BY <5>3, <3>dd
      <4> QED
        BY <4>cv, <4>lt, <4>4, <4>mvb, <3>c1
    <3>ee. CASE c1 < c
      <4> WITNESS Q \in Quorums
      <4> TAKE a \in Q
      <4>1. a \in Acceptors
        BY QuorumAssumption
      <4>2. PICK mm \in S : mm.acc = a
        BY <1>cov, <4>1
      <4>3. mm \in msgs /\ mm.type = "1b" /\ mm.bal = b
        BY <1>Smsgs, <4>2
      <4>4. mm.maxVBal =< c1
        BY <3>maxle, <4>2
      <4>5. /\ mm.bal =< maxBal[mm.acc]
            /\ \A cc \in (mm.maxVBal+1) .. (mm.bal-1) :
                  ~ \E vv \in Values : VotedForIn(mm.acc, vv, cc)
        BY <1>1b, <4>2
      <4>ma. maxBal[a] \in Int
        BY <4>1 DEF TypeOK
      <4>mvb. mm.maxVBal \in Int
        BY <1>Sint, <4>2
      <4>6. maxBal[a] >= b
        BY <4>5, <4>3, <4>2, <4>ma
      <4>7. c \in (mm.maxVBal+1) .. (mm.bal-1)
        BY <4>4, <4>3, <2>cb, <3>c1, <3>ee, <4>mvb
      <4>8. ~ \E vv \in Values : VotedForIn(a, vv, c)
        BY <4>5, <4>7, <4>2
      <4>9. WontVoteIn(a, c)
        BY <4>6, <4>8, <2>cb, <4>ma DEF WontVoteIn
      <4> QED
        BY <4>9
    <3> QED
      BY <3>cc, <3>dd, <3>ee, <2>cb, <3>c1
  <2> QED
    BY <2>A, <2>B
<1>1. TypeOK'
  BY <1>s DEF TypeOK, Messages
<1>2. MsgInv'
  <2> SUFFICES ASSUME NEW m \in msgs'
               PROVE  /\ (m.type = "1b") =>
                          /\ m.bal =< maxBal'[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
                          /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
                      /\ (m.type = "2a") =>
                          /\ SafeAt(m.val, m.bal)'
                          /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                      /\ (m.type = "2b") =>
                          /\ \E ma \in msgs' : /\ ma.type = "2a"
                                               /\ ma.bal  = m.bal
                                               /\ ma.val  = m.val
                          /\ m.bal =< maxVBal'[m.acc]
    BY DEF MsgInv
  <2>m. m \in msgs \/ m = m0
    BY <1>s
  <2>1. CASE m \in msgs
    <3>1. (m.type = "1b") =>
              /\ m.bal =< maxBal'[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
      BY <2>1, <1>s, <1>v DEF MsgInv
    <3>2. (m.type = "2a") =>
              /\ SafeAt(m.val, m.bal)'
              /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
      <4> SUFFICES ASSUME m.type = "2a"
                   PROVE  /\ SafeAt(m.val, m.bal)'
                          /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        OBVIOUS
      <4>1. m.val \in Values /\ m.bal \in Ballots
        BY <2>1 DEF TypeOK, Messages
      <4>2. SafeAt(m.val, m.bal)
        BY <2>1 DEF MsgInv
      <4>3. SafeAt(m.val, m.bal)'
        BY <4>1, <4>2, SafeAtStable, <1>n, <1>1
      <4>4. m.bal # b
        BY <2>1, <1>no2a
      <4>5. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        BY <2>1, <1>s, <4>4 DEF MsgInv
      <4> QED
        BY <4>3, <4>5
    <3>3. (m.type = "2b") =>
              /\ \E ma \in msgs' : /\ ma.type = "2a"
                                   /\ ma.bal  = m.bal
                                   /\ ma.val  = m.val
              /\ m.bal =< maxVBal'[m.acc]
      BY <2>1, <1>s DEF MsgInv
    <3> QED
      BY <3>1, <3>2, <3>3
  <2>2. CASE m = m0
    <3>1. m.type = "2a" /\ m.val = v /\ m.bal = b
      BY <2>2
    <3>2. SafeAt(v, b)'
      BY <1>safe, SafeAtStable, <1>n, <1>1
    <3>3. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = b) => (ma = m0)
      BY <1>s, <1>no2a
    <3> QED
      BY <3>1, <3>2, <3>3, <2>2
  <2>3. QED
    BY <2>1, <2>2, <2>m
<1>3. AccInv'
  BY <1>s, <1>v DEF AccInv
<1>4. QED
  BY <1>1, <1>2, <1>safe, <1>3 DEF Inv

LEMMA Phase1b_Inv ==
  ASSUME Inv, NEW a \in Acceptors, Phase1b(a)
  PROVE  Inv'
<1> USE DEF Ballots, Inv
<1>n. Next
  BY DEF Next
<1> PICK m1a \in msgs :
       /\ m1a.type = "1a"
       /\ m1a.bal > maxBal[a]
       /\ maxBal' = [maxBal EXCEPT ![a] = m1a.bal]
       /\ msgs' = msgs \cup {[type |-> "1b", bal |-> m1a.bal,
             maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a]}
       /\ maxVBal' = maxVBal /\ maxVal' = maxVal
  BY DEF Phase1b, Send
<1> DEFINE m0 == [type |-> "1b", bal |-> m1a.bal,
                  maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a]
<1>mbal. m1a.bal \in Ballots
  BY DEF TypeOK, Messages
<1>gt. m1a.bal > maxBal[a]
  OBVIOUS
<1>s. /\ msgs' = msgs \cup {m0}
      /\ maxBal' = [maxBal EXCEPT ![a] = m1a.bal]
      /\ maxVBal' = maxVBal /\ maxVal' = maxVal
  OBVIOUS
<1>v. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=> VotedForIn(aa, vv, bb)
  BY <1>s, VotedForIn_Send
<1>mb. \A aa \in Acceptors : maxBal[aa] =< maxBal'[aa]
  <2> TAKE aa \in Acceptors
  <2>1. maxBal'[aa] = IF aa = a THEN m1a.bal ELSE maxBal[aa]
    BY <1>s, <1>mbal DEF TypeOK
  <2>2. maxBal[aa] \in Int /\ maxBal[a] \in Int /\ m1a.bal \in Int
    BY <1>mbal DEF TypeOK
  <2> QED
    BY <2>1, <2>2, <1>gt
<1>1. TypeOK'
  <2>1. msgs' \in SUBSET Messages
    BY <1>s, <1>mbal DEF TypeOK, Messages
  <2>2. maxBal' \in [Acceptors -> Ballots \cup {-1}]
    BY <1>s, <1>mbal DEF TypeOK
  <2>3. \A aa \in Acceptors : maxBal'[aa] >= maxVBal'[aa]
    <3> TAKE aa \in Acceptors
    <3>1. maxBal'[aa] = IF aa = a THEN m1a.bal ELSE maxBal[aa]
      BY <1>s, <1>mbal DEF TypeOK
    <3>2. maxBal[aa] >= maxVBal[aa] /\ maxBal[a] >= maxVBal[a]
      BY DEF TypeOK
    <3>3. maxBal[aa] \in Int /\ maxVBal[aa] \in Int /\ maxBal[a] \in Int
          /\ maxVBal[a] \in Int /\ m1a.bal \in Int
      BY <1>mbal DEF TypeOK
    <3> QED
      BY <3>1, <3>2, <3>3, <1>gt, <1>s
  <2> QED
    BY <2>1, <2>2, <2>3, <1>s DEF TypeOK
<1>2. MsgInv'
  <2> SUFFICES ASSUME NEW m \in msgs'
               PROVE  /\ (m.type = "1b") =>
                          /\ m.bal =< maxBal'[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
                          /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
                      /\ (m.type = "2a") =>
                          /\ SafeAt(m.val, m.bal)'
                          /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                      /\ (m.type = "2b") =>
                          /\ \E ma \in msgs' : /\ ma.type = "2a"
                                               /\ ma.bal  = m.bal
                                               /\ ma.val  = m.val
                          /\ m.bal =< maxVBal'[m.acc]
    BY DEF MsgInv
  <2>m. m \in msgs \/ m = m0
    BY <1>s
  <2>1. CASE m \in msgs
    <3>1. (m.type = "1b") =>
              /\ m.bal =< maxBal'[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
      <4> SUFFICES ASSUME m.type = "1b"
                   PROVE  /\ m.bal =< maxBal'[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
                          /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
        OBVIOUS
      <4>0. m.acc \in Acceptors /\ m.bal \in Ballots
        BY <2>1 DEF TypeOK, Messages
      <4>1. /\ m.bal =< maxBal[m.acc]
            /\ \/ /\ m.maxVal \in Values
                  /\ m.maxVBal \in Ballots
                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
               \/ /\ m.maxVal = None
                  /\ m.maxVBal = -1
            /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                  ~ \E vv \in Values : VotedForIn(m.acc, vv, c)
        BY <2>1 DEF MsgInv
      <4>2. m.bal =< maxBal'[m.acc]
        BY <4>1, <4>0, <1>mb, <1>1 DEF TypeOK
      <4> QED
        BY <4>1, <4>2, <1>v
    <3>2. (m.type = "2a") =>
              /\ SafeAt(m.val, m.bal)'
              /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
      <4> SUFFICES ASSUME m.type = "2a"
                   PROVE  /\ SafeAt(m.val, m.bal)'
                          /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        OBVIOUS
      <4>1. m.val \in Values /\ m.bal \in Ballots
        BY <2>1 DEF TypeOK, Messages
      <4>2. SafeAt(m.val, m.bal)
        BY <2>1 DEF MsgInv
      <4>3. SafeAt(m.val, m.bal)'
        BY <4>1, <4>2, SafeAtStable, <1>n, <1>1
      <4>4. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        BY <2>1, <1>s DEF MsgInv
      <4> QED
        BY <4>3, <4>4
    <3>3. (m.type = "2b") =>
              /\ \E ma \in msgs' : /\ ma.type = "2a"
                                   /\ ma.bal  = m.bal
                                   /\ ma.val  = m.val
              /\ m.bal =< maxVBal'[m.acc]
      BY <2>1, <1>s DEF MsgInv
    <3> QED
      BY <3>1, <3>2, <3>3
  <2>2. CASE m = m0
    <3>1. m.type = "1b" /\ m.acc = a /\ m.bal = m1a.bal
          /\ m.maxVBal = maxVBal[a] /\ m.maxVal = maxVal[a]
      BY <2>2
    <3>2. m.bal =< maxBal'[m.acc]
      BY <3>1, <1>s, <1>mbal DEF TypeOK
    <3>3. \/ /\ m.maxVal \in Values
             /\ m.maxVBal \in Ballots
             /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
          \/ /\ m.maxVal = None
             /\ m.maxVBal = -1
      <4>1. (maxVal[a] = None) <=> (maxVBal[a] = -1)
        BY DEF AccInv
      <4>2. (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
        BY DEF AccInv
      <4>3. maxVBal[a] \in Ballots \cup {-1} /\ maxVal[a] \in Values \cup {None}
        BY DEF TypeOK
      <4>4. CASE maxVBal[a] = -1
        BY <4>1, <4>4, <3>1
      <4>5. CASE maxVBal[a] # -1
        <5>1. maxVBal[a] \in Ballots /\ maxVBal[a] >= 0
          BY <4>3, <4>5
        <5>2. maxVal[a] \in Values
          BY <4>1, <4>5, <4>3
        <5>3. VotedForIn(a, maxVal[a], maxVBal[a])
          BY <4>2, <5>1
        <5>4. VotedForIn(a, maxVal[a], maxVBal[a])'
          BY <5>3, <1>v
        <5> QED
          BY <5>1, <5>2, <5>4, <3>1
      <4> QED
        BY <4>4, <4>5
    <3>4. \A c \in (m.maxVBal+1) .. (m.bal-1) :
              ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
      <4> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1)
                   PROVE  ~ \E vv \in Values : VotedForIn(a, vv, c)'
        BY <3>1
      <4>0. maxVBal[a] \in Int /\ maxVBal[a] >= -1 /\ m1a.bal \in Int
        BY <1>mbal DEF TypeOK
      <4>1. c \in Ballots /\ c > maxVBal[a]
        BY <3>1, <4>0, <1>mbal
      <4>2. ~ \E vv \in Values : VotedForIn(a, vv, c)
        BY <4>1 DEF AccInv
      <4> QED
        BY <4>2, <1>v
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4
  <2>3. QED
    BY <2>1, <2>2, <2>m
<1>3. AccInv'
  <2> SUFFICES ASSUME NEW aa \in Acceptors
               PROVE  /\ (maxVal'[aa] = None) <=> (maxVBal'[aa] = -1)
                      /\ maxVBal'[aa] =< maxBal'[aa]
                      /\ (maxVBal'[aa] >= 0) => VotedForIn(aa, maxVal[aa], maxVBal[aa])'
                      /\ \A c \in Ballots :
                            c > maxVBal'[aa] => ~ \E vv \in Values : VotedForIn(aa, vv, c)'
    BY DEF AccInv
  <2>1. (maxVal'[aa] = None) <=> (maxVBal'[aa] = -1)
    BY <1>s DEF AccInv
  <2>2. maxVBal'[aa] =< maxBal'[aa]
    <3>1. maxBal'[aa] = IF aa = a THEN m1a.bal ELSE maxBal[aa]
      BY <1>s, <1>mbal DEF TypeOK
    <3>2. maxVBal[aa] =< maxBal[aa] /\ maxVBal[a] =< maxBal[a]
      BY DEF AccInv
    <3>3. maxVBal[aa] \in Int /\ maxBal[aa] \in Int /\ maxBal[a] \in Int
          /\ maxVBal[a] \in Int /\ m1a.bal \in Int
      BY <1>mbal DEF TypeOK
    <3> QED
      BY <3>1, <3>2, <3>3, <1>gt, <1>s
  <2>3. (maxVBal'[aa] >= 0) => VotedForIn(aa, maxVal[aa], maxVBal[aa])'
    BY <1>s, <1>v DEF AccInv
  <2>4. \A c \in Ballots : c > maxVBal'[aa] => ~ \E vv \in Values : VotedForIn(aa, vv, c)'
    BY <1>s, <1>v DEF AccInv
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA Phase2b_Inv ==
  ASSUME Inv, NEW a \in Acceptors, Phase2b(a)
  PROVE  Inv'
<1> USE DEF Ballots, Inv
<1>n. Next
  BY DEF Next
<1> PICK m2a \in msgs :
       /\ m2a.type = "2a"
       /\ m2a.bal >= maxBal[a]
       /\ maxVBal' = [maxVBal EXCEPT ![a] = m2a.bal]
       /\ maxBal' = [maxBal EXCEPT ![a] = m2a.bal]
       /\ maxVal' = [maxVal EXCEPT ![a] = m2a.val]
       /\ msgs' = msgs \cup {[type |-> "2b", bal |-> m2a.bal, val |-> m2a.val, acc |-> a]}
  BY DEF Phase2b, Send
<1> DEFINE m0 == [type |-> "2b", bal |-> m2a.bal, val |-> m2a.val, acc |-> a]
<1>tp. m2a.bal \in Ballots /\ m2a.val \in Values
  BY DEF TypeOK, Messages
<1>ge. m2a.bal >= maxBal[a]
  OBVIOUS
<1>s. /\ msgs' = msgs \cup {m0}
      /\ maxVBal' = [maxVBal EXCEPT ![a] = m2a.bal]
      /\ maxBal' = [maxBal EXCEPT ![a] = m2a.bal]
      /\ maxVal' = [maxVal EXCEPT ![a] = m2a.val]
  OBVIOUS
<1>vc. \A aa, vv, bb : VotedForIn(aa, vv, bb)' <=>
          (VotedForIn(aa, vv, bb) \/ (vv = m2a.val /\ bb = m2a.bal /\ aa = a))
  BY <1>s, VotedForIn_Send
<1>nv. VotedForIn(a, m2a.val, m2a.bal)'
  BY <1>vc
<1>1. TypeOK'
  <2>1. msgs' \in SUBSET Messages
    BY <1>s, <1>tp DEF TypeOK, Messages
  <2>2. maxVBal' \in [Acceptors -> Ballots \cup {-1}]
    BY <1>s, <1>tp DEF TypeOK
  <2>3. maxBal' \in [Acceptors -> Ballots \cup {-1}]
    BY <1>s, <1>tp DEF TypeOK
  <2>4. maxVal' \in [Acceptors -> Values \cup {None}]
    BY <1>s, <1>tp DEF TypeOK
  <2>5. \A aa \in Acceptors : maxBal'[aa] >= maxVBal'[aa]
    <3> TAKE aa \in Acceptors
    <3>1. maxBal'[aa] = IF aa = a THEN m2a.bal ELSE maxBal[aa]
      BY <1>s, <1>tp DEF TypeOK
    <3>2. maxVBal'[aa] = IF aa = a THEN m2a.bal ELSE maxVBal[aa]
      BY <1>s, <1>tp DEF TypeOK
    <3>3. maxBal[aa] >= maxVBal[aa]
      BY DEF TypeOK
    <3>4. maxBal[aa] \in Int /\ maxVBal[aa] \in Int /\ m2a.bal \in Int
      BY <1>tp DEF TypeOK
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
<1>2. MsgInv'
  <2> SUFFICES ASSUME NEW m \in msgs'
               PROVE  /\ (m.type = "1b") =>
                          /\ m.bal =< maxBal'[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
                          /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
                      /\ (m.type = "2a") =>
                          /\ SafeAt(m.val, m.bal)'
                          /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
                      /\ (m.type = "2b") =>
                          /\ \E ma \in msgs' : /\ ma.type = "2a"
                                               /\ ma.bal  = m.bal
                                               /\ ma.val  = m.val
                          /\ m.bal =< maxVBal'[m.acc]
    BY DEF MsgInv
  <2>m. m \in msgs \/ m = m0
    BY <1>s
  <2>1. CASE m \in msgs
    <3>1. (m.type = "1b") =>
              /\ m.bal =< maxBal'[m.acc]
              /\ \/ /\ m.maxVal \in Values
                    /\ m.maxVBal \in Ballots
                    /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                 \/ /\ m.maxVal = None
                    /\ m.maxVBal = -1
              /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                    ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
      <4> SUFFICES ASSUME m.type = "1b"
                   PROVE  /\ m.bal =< maxBal'[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
                          /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                                ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
        OBVIOUS
      <4>0. m.acc \in Acceptors /\ m.bal \in Ballots /\ m.maxVBal \in Int
        BY <2>1 DEF TypeOK, Messages
      <4>1. /\ m.bal =< maxBal[m.acc]
            /\ \/ /\ m.maxVal \in Values
                  /\ m.maxVBal \in Ballots
                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)
               \/ /\ m.maxVal = None
                  /\ m.maxVBal = -1
            /\ \A c \in (m.maxVBal+1) .. (m.bal-1) :
                  ~ \E vv \in Values : VotedForIn(m.acc, vv, c)
        BY <2>1 DEF MsgInv
      <4>bal. m.bal =< maxBal'[m.acc]
        <5>1. maxBal'[m.acc] = IF m.acc = a THEN m2a.bal ELSE maxBal[m.acc]
          BY <1>s, <1>tp, <4>0 DEF TypeOK
        <5>2. m.bal =< maxBal[m.acc]
          BY <4>1
        <5>3. m.bal \in Int /\ maxBal[m.acc] \in Int /\ maxBal[a] \in Int /\ m2a.bal \in Int
          BY <4>0, <1>tp DEF TypeOK
        <5> QED
          BY <5>1, <5>2, <5>3, <1>ge
      <4>disj. \/ /\ m.maxVal \in Values
                  /\ m.maxVBal \in Ballots
                  /\ VotedForIn(m.acc, m.maxVal, m.maxVBal)'
               \/ /\ m.maxVal = None
                  /\ m.maxVBal = -1
        BY <4>1, <1>vc
      <4>nov. \A c \in (m.maxVBal+1) .. (m.bal-1) :
                  ~ \E vv \in Values : VotedForIn(m.acc, vv, c)'
        <5> SUFFICES ASSUME NEW c \in (m.maxVBal+1) .. (m.bal-1),
                            NEW vv \in Values, VotedForIn(m.acc, vv, c)'
                     PROVE  FALSE
          OBVIOUS
        <5>0. m.bal \in Int /\ maxBal[a] \in Int /\ m2a.bal \in Int /\ c \in Int
          BY <4>0, <1>tp DEF TypeOK
        <5>1. ~ VotedForIn(m.acc, vv, c)
          BY <4>1
        <5>2. vv = m2a.val /\ c = m2a.bal /\ m.acc = a
          BY <1>vc, <5>1
        <5>3. c =< m.bal - 1
          BY <4>0
        <5>4. m.bal =< maxBal[a]
          BY <4>1, <5>2
        <5> QED
          BY <5>2, <5>3, <5>4, <1>ge, <5>0
      <4> QED
        BY <4>bal, <4>disj, <4>nov
    <3>2. (m.type = "2a") =>
              /\ SafeAt(m.val, m.bal)'
              /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
      <4> SUFFICES ASSUME m.type = "2a"
                   PROVE  /\ SafeAt(m.val, m.bal)'
                          /\ \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        OBVIOUS
      <4>1. m.val \in Values /\ m.bal \in Ballots
        BY <2>1 DEF TypeOK, Messages
      <4>2. SafeAt(m.val, m.bal)
        BY <2>1 DEF MsgInv
      <4>3. SafeAt(m.val, m.bal)'
        BY <4>1, <4>2, SafeAtStable, <1>n, <1>1
      <4>4. \A ma \in msgs' : (ma.type = "2a") /\ (ma.bal = m.bal) => (ma = m)
        BY <2>1, <1>s DEF MsgInv
      <4> QED
        BY <4>3, <4>4
    <3>3. (m.type = "2b") =>
              /\ \E ma \in msgs' : /\ ma.type = "2a"
                                   /\ ma.bal  = m.bal
                                   /\ ma.val  = m.val
              /\ m.bal =< maxVBal'[m.acc]
      <4> SUFFICES ASSUME m.type = "2b"
                   PROVE  /\ \E ma \in msgs' : /\ ma.type = "2a"
                                               /\ ma.bal  = m.bal
                                               /\ ma.val  = m.val
                          /\ m.bal =< maxVBal'[m.acc]
        OBVIOUS
      <4>0. m.acc \in Acceptors
        BY <2>1 DEF TypeOK, Messages
      <4>1. /\ \E ma \in msgs : ma.type = "2a" /\ ma.bal = m.bal /\ ma.val = m.val
            /\ m.bal =< maxVBal[m.acc]
        BY <2>1 DEF MsgInv
      <4>2. \E ma \in msgs' : ma.type = "2a" /\ ma.bal = m.bal /\ ma.val = m.val
        BY <4>1, <1>s
      <4>3. m.bal =< maxVBal'[m.acc]
        <5>1. maxVBal'[m.acc] = IF m.acc = a THEN m2a.bal ELSE maxVBal[m.acc]
          BY <1>s, <1>tp, <4>0 DEF TypeOK
        <5>2. m.bal =< maxVBal[m.acc]
          BY <4>1
        <5>3. maxVBal[a] =< maxBal[a]
          BY DEF AccInv
        <5>4. m.bal \in Int /\ maxVBal[m.acc] \in Int /\ maxVBal[a] \in Int
              /\ maxBal[a] \in Int /\ m2a.bal \in Int
          BY <4>0, <2>1, <1>tp DEF TypeOK, Messages
        <5> QED
          BY <5>1, <5>2, <5>3, <5>4, <1>ge
      <4> QED
        BY <4>2, <4>3
    <3> QED
      BY <3>1, <3>2, <3>3
  <2>2. CASE m = m0
    <3>1. m.type = "2b" /\ m.bal = m2a.bal /\ m.val = m2a.val /\ m.acc = a
      BY <2>2
    <3>2. \E ma \in msgs' : ma.type = "2a" /\ ma.bal = m2a.bal /\ ma.val = m2a.val
      BY <1>s
    <3>3. m.bal =< maxVBal'[m.acc]
      BY <3>1, <1>s, <1>tp DEF TypeOK
    <3> QED
      BY <3>1, <3>2, <3>3
  <2>3. QED
    BY <2>1, <2>2, <2>m
<1>3. AccInv'
  <2> SUFFICES ASSUME NEW aa \in Acceptors
               PROVE  /\ (maxVal'[aa] = None) <=> (maxVBal'[aa] = -1)
                      /\ maxVBal'[aa] =< maxBal'[aa]
                      /\ (maxVBal'[aa] >= 0) => VotedForIn(aa, maxVal[aa], maxVBal[aa])'
                      /\ \A c \in Ballots :
                            c > maxVBal'[aa] => ~ \E vv \in Values : VotedForIn(aa, vv, c)'
    BY DEF AccInv
  <2>bal. maxBal'[aa] = IF aa = a THEN m2a.bal ELSE maxBal[aa]
    BY <1>s, <1>tp DEF TypeOK
  <2>vbal. maxVBal'[aa] = IF aa = a THEN m2a.bal ELSE maxVBal[aa]
    BY <1>s, <1>tp DEF TypeOK
  <2>val. maxVal'[aa] = IF aa = a THEN m2a.val ELSE maxVal[aa]
    BY <1>s, <1>tp DEF TypeOK
  <2>acc. /\ (maxVal[aa] = None) <=> (maxVBal[aa] = -1)
          /\ maxVBal[aa] =< maxBal[aa]
          /\ (maxVBal[aa] >= 0) => VotedForIn(aa, maxVal[aa], maxVBal[aa])
          /\ \A c \in Ballots : c > maxVBal[aa] => ~ \E vv \in Values : VotedForIn(aa, vv, c)
    BY DEF AccInv
  <2>int. maxVBal[aa] \in Int /\ maxBal[aa] \in Int /\ maxBal[a] \in Int
          /\ maxVBal[a] \in Int /\ m2a.bal \in Int
    BY <1>tp DEF TypeOK
  <2>1. (maxVal'[aa] = None) <=> (maxVBal'[aa] = -1)
    <3>1. CASE aa = a
      BY <3>1, <2>val, <2>vbal, <1>tp, NoneNotInValues
    <3>2. CASE aa # a
      BY <3>2, <2>val, <2>vbal, <2>acc
    <3> QED
      BY <3>1, <3>2
  <2>2. maxVBal'[aa] =< maxBal'[aa]
    BY <2>bal, <2>vbal, <2>acc, <2>int, <1>ge
  <2>3. (maxVBal'[aa] >= 0) => VotedForIn(aa, maxVal[aa], maxVBal[aa])'
    <3> SUFFICES ASSUME maxVBal'[aa] >= 0
                 PROVE  VotedForIn(aa, maxVal[aa], maxVBal[aa])'
      OBVIOUS
    <3>1. CASE aa = a
      <4>1. maxVal'[a] = m2a.val /\ maxVBal'[a] = m2a.bal
        BY <3>1, <2>val, <2>vbal
      <4> QED
        BY <3>1, <4>1, <1>s DEF VotedForIn
    <3>2. CASE aa # a
      <4>1. maxVBal[aa] >= 0
        BY <3>2, <2>vbal
      <4>2. VotedForIn(aa, maxVal[aa], maxVBal[aa])
        BY <4>1, <2>acc
      <4>3. maxVal'[aa] = maxVal[aa] /\ maxVBal'[aa] = maxVBal[aa]
        BY <3>2, <2>val, <2>vbal
      <4>4. PICK mm \in msgs : mm.type = "2b" /\ mm.val = maxVal[aa]
                               /\ mm.bal = maxVBal[aa] /\ mm.acc = aa
        BY <4>2 DEF VotedForIn
      <4> QED
        BY <4>3, <4>4, <1>s DEF VotedForIn
    <3> QED
      BY <3>1, <3>2
  <2>4. \A c \in Ballots : c > maxVBal'[aa] => ~ \E vv \in Values : VotedForIn(aa, vv, c)'
    <3> SUFFICES ASSUME NEW c \in Ballots, c > maxVBal'[aa],
                        NEW vv \in Values, VotedForIn(aa, vv, c)'
                 PROVE  FALSE
      OBVIOUS
    <3>1. VotedForIn(aa, vv, c) \/ (vv = m2a.val /\ c = m2a.bal /\ aa = a)
      BY <1>vc
    <3>2. CASE aa = a
      <4>1. c > m2a.bal
        BY <3>2, <2>vbal
      <4>2. c # m2a.bal
        BY <4>1, <2>int
      <4>3. VotedForIn(a, vv, c)
        BY <3>1, <3>2, <4>2
      <4>4. c > maxVBal[a]
        BY <4>1, <1>ge, <2>acc, <2>int, <3>2
      <4> QED
        BY <4>3, <4>4, <2>acc, <3>2
    <3>3. CASE aa # a
      <4>1. VotedForIn(aa, vv, c)
        BY <3>1, <3>3
      <4>2. c > maxVBal[aa]
        BY <3>3, <2>vbal
      <4> QED
        BY <4>1, <4>2, <2>acc
    <3> QED
      BY <3>2, <3>3
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Inv

THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE Next
    <3>1. CASE \E b \in Ballots : Phase1a(b)
      BY <3>1, Phase1a_Inv
    <3>2. CASE \E b \in Ballots : Phase2a(b)
      BY <3>2, Phase2a_Inv
    <3>3. CASE \E aa \in Acceptors : Phase1b(aa)
      BY <3>3, Phase1b_Inv
    <3>4. CASE \E aa \in Acceptors : Phase2b(aa)
      BY <3>4, Phase2b_Inv
    <3> QED
      BY <2>1, <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>2. CASE vars' = vars
    <3>1. msgs' = msgs /\ maxBal' = maxBal /\ maxVBal' = maxVBal /\ maxVal' = maxVal
      BY <2>2 DEF vars
    <3> QED
      BY <3>1 DEF Inv, TypeOK, MsgInv, AccInv, VotedForIn, SafeAt, WontVoteIn
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

    

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