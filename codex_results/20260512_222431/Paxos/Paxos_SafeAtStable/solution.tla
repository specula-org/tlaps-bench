------------------------------- MODULE Paxos_SafeAtStable -------------------------------
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
<1> SUFFICES ASSUME Inv, Next, TypeOK',
                    NEW v \in Values, NEW b \in Ballots, SafeAt(v, b)
             PROVE  SafeAt(v, b)'
  OBVIOUS
<1> USE DEF Send, Inv, Ballots
<1>1. ASSUME NEW bb \in Ballots, Phase1a(bb)
      PROVE  SafeAt(v, b)'
  BY <1>1 DEF SafeAt, Phase1a, VotedForIn, WontVoteIn
<1>2. ASSUME NEW a \in Acceptors, Phase1b(a)
      PROVE  SafeAt(v, b)'
  BY <1>2, QuorumAssumption DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase1b
<1>3. ASSUME NEW bb \in Ballots, Phase2a(bb)
      PROVE  SafeAt(v, b)'
  BY <1>3, QuorumAssumption DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase2a
<1>4. ASSUME NEW a \in Acceptors, Phase2b(a)
      PROVE  SafeAt(v, b)'
  <2>1. PICK m \in msgs : Phase2b(a)!(m)
    BY <1>4, Zenon DEF Phase2b
  <2>2. \A aa \in Acceptors, bb \in Ballots, vv \in Values :
            VotedForIn(aa, vv, bb) => VotedForIn(aa, vv, bb)'
    BY <2>1 DEF TypeOK, VotedForIn
  <2>3. \A aa \in Acceptors, bb \in Ballots : maxBal[aa] > bb => maxBal'[aa] > bb
    BY <2>1 DEF TypeOK
  <2>4. ASSUME NEW aa \in Acceptors, NEW bb \in Ballots,
               WontVoteIn(aa, bb), NEW vv \in Values,
               VotedForIn(aa, vv, bb)'
        PROVE FALSE
    <3> DEFINE mm == [type |-> "2b", val |-> vv, bal |-> bb, acc |-> aa]
    <3>1. mm \notin msgs
      BY <2>4 DEF WontVoteIn, VotedForIn
    <3>2. mm \in msgs'
      <4>1. PICK m1 \in msgs' :
              /\ m1.type = "2b"
              /\ m1.val = vv
              /\ m1.bal = bb
              /\ m1.acc = aa
        BY <2>4 DEF VotedForIn
      <4>. QED  BY <4>1 DEF TypeOK, Messages
    <3>3. aa = a /\ m.bal = bb
      BY <2>1, <3>1, <3>2 DEF TypeOK
    <3>. QED
      BY <2>1, <2>4, <3>3 DEF Phase2b, WontVoteIn, TypeOK 
  <2>5. \A aa \in Acceptors, bb \in Ballots : WontVoteIn(aa, bb) => WontVoteIn(aa, bb)'
    BY <2>3, <2>4 DEF WontVoteIn
  <2> QED
    BY <2>2, <2>5, QuorumAssumption DEF SafeAt
<1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

=============================================================================
