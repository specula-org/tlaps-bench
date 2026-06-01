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
PROOF
  <1>1. ASSUME Inv, Next, TypeOK'
        PROVE  \A v \in Values, b \in Ballots:
                 SafeAt(v, b) => SafeAt(v, b)'
    <2>1. ASSUME NEW v \in Values, NEW b \in Ballots
          PROVE SafeAt(v, b) => SafeAt(v, b)'
      <3>1. ASSUME SafeAt(v, b)
            PROVE SafeAt(v, b)'
        <4>1. ASSUME NEW c \in 0..(b-1)
              PROVE \E Q \in Quorums :
                      \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
          <5>1. PICK Q \in Quorums :
                  \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)
            BY <3>1, <4>1 DEF SafeAt
          <5>2. \A a \in Q : VotedForIn(a, v, c) => VotedForIn(a, v, c)'
            <6>1. ASSUME NEW a \in Q, VotedForIn(a, v, c)
                  PROVE VotedForIn(a, v, c)'
              <7>1. PICK m \in msgs :
                      /\ m.type = "2b"
                      /\ m.val  = v
                      /\ m.bal  = c
                      /\ m.acc  = a
                BY <6>1 DEF VotedForIn
              <7>2. msgs \subseteq msgs'
                BY <1>1 DEF Next, Phase1a, Phase1b, Phase2a, Phase2b, Send
              <7>3. m \in msgs'
                BY <7>1, <7>2
              <7>. QED
                BY <7>1, <7>3 DEF VotedForIn
            <6>. QED
          <5>3. \A a \in Q : WontVoteIn(a, c) => WontVoteIn(a, c)'
            <6>1. ASSUME NEW a \in Q, WontVoteIn(a, c)
                  PROVE WontVoteIn(a, c)'
              <7>1. maxBal'[a] >= maxBal[a]
                <8>1. a \in Acceptors
                  BY QuorumAssumption, <5>1, <6>1
                <8>2. maxBal[a] \in Int
                  BY <1>1, <8>1 DEF Inv, TypeOK, Ballots
                <8>3. maxBal'[a] \in Int
                  BY <1>1, <8>1 DEF TypeOK, Ballots
                <8>4. \A d \in Ballots : Phase1a(d) => maxBal'[a] = maxBal[a]
                  BY DEF Phase1a
                <8>5. \A d \in Ballots : Phase2a(d) => maxBal'[a] = maxBal[a]
                  BY DEF Phase2a
                <8>6. \A aa \in Acceptors : Phase1b(aa) => maxBal'[a] >= maxBal[a]
                  <9>1. ASSUME NEW aa \in Acceptors, Phase1b(aa)
                        PROVE maxBal'[a] >= maxBal[a]
                    <10>1. PICK m \in msgs :
                             /\ m.type = "1a"
                             /\ m.bal > maxBal[aa]
                             /\ maxBal' = [maxBal EXCEPT ![aa] = m.bal]
                      BY <9>1 DEF Phase1b
                    <10>2. CASE a = aa
                      <11>1. maxBal'[a] = m.bal
                        BY <1>1, <8>1, <9>1, <10>1, <10>2 DEF Inv, TypeOK
                      <11>2. maxBal'[a] > maxBal[a]
                        BY <8>2, <10>1, <10>2, <11>1, SimpleArithmetic DEF Ballots
                      <11>3. maxBal'[a] >= maxBal[a]
                        BY <8>2, <8>3, <11>2, SimpleArithmetic
                      <11>. QED
                        BY <11>3
                    <10>3. CASE a # aa
                      <11>1. maxBal'[a] = maxBal[a]
                        BY <1>1, <8>1, <9>1, <10>1, <10>3 DEF Inv, TypeOK
                      <11>. QED
                        BY <8>2, <8>3, <11>1, SimpleArithmetic
                    <10>. QED
                      BY <10>2, <10>3, SMT
                  <9>. QED
                <8>7. \A aa \in Acceptors : Phase2b(aa) => maxBal'[a] >= maxBal[a]
                  <9>1. ASSUME NEW aa \in Acceptors, Phase2b(aa)
                        PROVE maxBal'[a] >= maxBal[a]
                    <10>1. PICK m \in msgs :
                             /\ m.type = "2a"
                             /\ m.bal >= maxBal[aa]
                             /\ maxBal' = [maxBal EXCEPT ![aa] = m.bal]
                      BY <9>1 DEF Phase2b
                    <10>2. CASE a = aa
                      <11>1. maxBal'[a] = m.bal
                        BY <1>1, <8>1, <9>1, <10>1, <10>2 DEF Inv, TypeOK
                      <11>. QED
                        BY <8>2, <8>3, <10>1, <10>2, <11>1, SimpleArithmetic DEF Ballots
                    <10>3. CASE a # aa
                      <11>1. maxBal'[a] = maxBal[a]
                        BY <1>1, <8>1, <9>1, <10>1, <10>3 DEF Inv, TypeOK
                      <11>. QED
                        BY <8>2, <8>3, <11>1, SimpleArithmetic
                    <10>. QED
                      BY <10>2, <10>3, SMT
                  <9>. QED
                <8>8. (\E d \in Ballots : Phase1a(d))
                       \/ (\E d \in Ballots : Phase2a(d))
                       \/ (\E aa \in Acceptors : Phase1b(aa))
                       \/ (\E aa \in Acceptors : Phase2b(aa))
                  BY <1>1 DEF Next
                <8>9. CASE \E d \in Ballots : Phase1a(d)
                  BY <8>2, <8>3, <8>4, <8>9, SimpleArithmetic
                <8>10. CASE \E d \in Ballots : Phase2a(d)
                  BY <8>2, <8>3, <8>5, <8>10, SimpleArithmetic
                <8>11. CASE \E aa \in Acceptors : Phase1b(aa)
                  BY <8>6, <8>11
                <8>12. CASE \E aa \in Acceptors : Phase2b(aa)
                  BY <8>7, <8>12
                <8>. QED
                  BY <8>8, <8>9, <8>10, <8>11, <8>12
              <7>2. maxBal'[a] > c
                <8>1. maxBal[a] > c
                  BY <6>1 DEF WontVoteIn
                <8>2. c \in Int
                  BY <4>1, SimpleArithmetic DEF Ballots
                <8>3. a \in Acceptors
                  BY QuorumAssumption, <5>1, <6>1
                <8>4. maxBal'[a] \in Int
                  BY <1>1, <8>3 DEF TypeOK, Ballots
                <8>5. maxBal[a] \in Int
                  BY <1>1, <8>3 DEF Inv, TypeOK, Ballots
                <8>. QED
                  BY <7>1, <8>1, <8>2, <8>4, <8>5, SimpleArithmetic
              <7>3. \A vv \in Values : ~ VotedForIn(a, vv, c)'
                <8>1. ASSUME NEW vv \in Values, VotedForIn(a, vv, c)'
                      PROVE FALSE
                  <9>1. PICK mm \in msgs' :
                          /\ mm.type = "2b"
                          /\ mm.val  = vv
                          /\ mm.bal  = c
                          /\ mm.acc  = a
                    BY <8>1 DEF VotedForIn
                  <9>2. CASE mm \in msgs
                    BY <6>1, <9>1, <9>2 DEF WontVoteIn, VotedForIn
                  <9>3. CASE mm \notin msgs
                    <10>1. mm.bal >= maxBal[a]
                      BY <1>1, <9>1, <9>3 DEF Next, Phase1a, Phase1b, Phase2a, Phase2b, Send
                    <10>2. FALSE
                      <11>1. maxBal[a] > c
                        BY <6>1 DEF WontVoteIn
                      <11>2. c \in Int
                        BY <4>1, SimpleArithmetic DEF Ballots
                      <11>3. a \in Acceptors
                        BY QuorumAssumption, <5>1, <6>1
                      <11>4. maxBal[a] \in Int
                        BY <1>1, <11>3 DEF Inv, TypeOK, Ballots
                      <11>. QED
                        BY <9>1, <10>1, <11>1, <11>2, <11>4, SimpleArithmetic
                    <10>. QED
                      BY <10>2
                  <9>4. QED
                    BY <9>2, <9>3
                <8>. QED
              <7>. QED
                BY <7>2, <7>3 DEF WontVoteIn
            <6>. QED
          <5>4. \A a \in Q : VotedForIn(a, v, c)' \/ WontVoteIn(a, c)'
            BY <5>1, <5>2, <5>3
          <5>. QED
            BY <5>1, <5>4
        <4>. QED
          BY <4>1 DEF SafeAt
      <3>. QED
    <2>. QED
  <1>. QED


=============================================================================
