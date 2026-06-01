----------------------------- MODULE VoteProof_VT2 ------------------------------

EXTENDS Integers , FiniteSets, TLC, TLAPS

-----------------------------------------------------------------------------
CONSTANT Value,     
         Acceptor,  
         Quorum     

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  
 
-----------------------------------------------------------------------------

Ballot == Nat
-----------------------------------------------------------------------------

VARIABLES votes, maxBal

VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

SafeAt(b, v) ==
  LET SA[bb \in Ballot] ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
  IN  SA[b]

vars == << votes, maxBal >>

Init == 
        /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

acceptor(self) == \E b \in Ballot:
                    \/ /\ b > maxBal[self]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ UNCHANGED votes
                    \/ /\ \E v \in Value:
                            /\ /\ maxBal[self] \leq b
                               /\ DidNotVoteIn(self, b)
                               /\ \A p \in Acceptor \ {self} :
                                     \A w \in Value : VotedFor(p, b, w) => (w = v)
                               /\ SafeAt(b, v)
                            /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]

Next == (\E self \in Acceptor: acceptor(self))

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

-----------------------------------------------------------------------------

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
                  VotedFor(a, b, v) => SafeAt(b, v)

VInv3 ==  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
                VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

VInv4 == \A a \in Acceptor, b \in Ballot : 
            maxBal[a] < b => DidNotVoteIn(a, b)

VInv == TypeOK /\ VInv2 /\ VInv3 /\ VInv4
-----------------------------------------------------------------------------

ASSUME AcceptorNonempty == Acceptor # {}

-----------------------------------------------------------------------------

(***************************************************************************)
(* Scaffolding for the inductive-invariance proof of VT2.                  *)
(***************************************************************************)

NI == INSTANCE NaturalsInduction

IncreaseMaxBal(self, b) ==
  /\ b > maxBal[self]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED votes

VoteFor(self, b, v) ==
  /\ maxBal[self] \leq b
  /\ DidNotVoteIn(self, b)
  /\ \A p \in Acceptor \ {self} :
        \A w \in Value : VotedFor(p, b, w) => (w = v)
  /\ SafeAt(b, v)
  /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]

BallotAction(self, b) ==
  \/ IncreaseMaxBal(self, b)
  \/ \E v \in Value : VoteFor(self, b, v)

LEMMA NextDef ==
  Next = \E self \in Acceptor : \E b \in Ballot : BallotAction(self, b)
BY DEF Next, acceptor, BallotAction, IncreaseMaxBal, VoteFor

-----------------------------------------------------------------------------

LEMMA SafeAtProp ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v) =
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w) => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
<1>1. ASSUME NEW v \in Value
      PROVE  \A b \in Ballot :
               SafeAt(b, v) =
                 \/ b = 0
                 \/ \E Q \in Quorum :
                      /\ \A a \in Q : maxBal[a] \geq b
                      /\ \E c \in -1..(b-1) :
                           /\ (c # -1) => /\ SafeAt(c, v)
                                          /\ \A a \in Q :
                                               \A w \in Value :
                                                  VotedFor(a, c, w) => (w = v)
                           /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
  <2> DEFINE op(g, bb) ==
               \/ bb = 0
               \/ \E Q \in Quorum :
                    /\ \A a \in Q : maxBal[a] \geq bb
                    /\ \E c \in -1..(bb-1) :
                         /\ (c # -1) => /\ g[c]
                                        /\ \A a \in Q :
                                             \A w \in Value :
                                                VotedFor(a, c, w) => (w = v)
                         /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
             SA[bb \in Nat] == op(SA, bb)
  <2>1. \A bb \in Ballot : SafeAt(bb, v) = SA[bb]
    BY DEF SafeAt, Ballot, op
  <2>2. SA = [bb \in Nat |-> op(SA, bb)]
    <3>1. ASSUME NEW n \in Nat, NEW g, NEW h, \A i \in 0..(n-1) : g[i] = h[i]
          PROVE  op(g, n) = op(h, n)
      BY <3>1, Z3 DEF op
    <3> HIDE DEF op
    <3>2. QED
      BY <3>1, NI!RecursiveFcnOfNat, Isa
  <2>3. ASSUME NEW b \in Ballot
        PROVE  SafeAt(b, v) =
                 \/ b = 0
                 \/ \E Q \in Quorum :
                      /\ \A a \in Q : maxBal[a] \geq b
                      /\ \E c \in -1..(b-1) :
                           /\ (c # -1) => /\ SafeAt(c, v)
                                          /\ \A a \in Q :
                                               \A w \in Value :
                                                  VotedFor(a, c, w) => (w = v)
                           /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
    <3> HIDE DEF op, SA, SafeAt
    <3>0. b \in Nat
      BY DEF Ballot
    <3>1. SafeAt(b, v) = SA[b]
      BY <2>1
    <3>2. SA[b] = op(SA, b)
      BY <2>2, <3>0
    <3>3a. \A c \in 0..(b-1) : SA[c] = SafeAt(c, v)
      BY <2>1 DEF Ballot
    <3>3. \A c \in -1..(b-1) : (c # -1) => (SA[c] = SafeAt(c, v))
      BY <3>3a, <3>0
    <3>4. op(SA, b) =
            \/ b = 0
            \/ \E Q \in Quorum :
                 /\ \A a \in Q : maxBal[a] \geq b
                 /\ \E c \in -1..(b-1) :
                      /\ (c # -1) => /\ SafeAt(c, v)
                                     /\ \A a \in Q :
                                          \A w \in Value :
                                             VotedFor(a, c, w) => (w = v)
                      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
      BY <3>3 DEF op
    <3>5. QED
      BY <3>1, <3>2, <3>4
  <2>4. QED
    BY <2>3
<1>2. QED
  BY <1>1

-----------------------------------------------------------------------------

LEMMA SafeAtPropPrime ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v)' =
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal'[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)'
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w)' => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)'
<1>1. ASSUME NEW v \in Value
      PROVE  \A b \in Ballot :
               SafeAt(b, v)' =
                 \/ b = 0
                 \/ \E Q \in Quorum :
                      /\ \A a \in Q : maxBal'[a] \geq b
                      /\ \E c \in -1..(b-1) :
                           /\ (c # -1) => /\ SafeAt(c, v)'
                                          /\ \A a \in Q :
                                               \A w \in Value :
                                                  VotedFor(a, c, w)' => (w = v)
                           /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)'
  <2> DEFINE op(g, bb) ==
               \/ bb = 0
               \/ \E Q \in Quorum :
                    /\ \A a \in Q : maxBal'[a] \geq bb
                    /\ \E c \in -1..(bb-1) :
                         /\ (c # -1) => /\ g[c]
                                        /\ \A a \in Q :
                                             \A w \in Value :
                                                VotedFor(a, c, w)' => (w = v)
                         /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)'
             SA[bb \in Nat] == op(SA, bb)
  <2>1. \A bb \in Ballot : SafeAt(bb, v)' = SA[bb]
    BY DEF SafeAt, Ballot, op
  <2>2. SA = [bb \in Nat |-> op(SA, bb)]
    <3>1. ASSUME NEW n \in Nat, NEW g, NEW h, \A i \in 0..(n-1) : g[i] = h[i]
          PROVE  op(g, n) = op(h, n)
      BY <3>1, Z3 DEF op
    <3> HIDE DEF op
    <3>2. QED
      BY <3>1, NI!RecursiveFcnOfNat, Isa
  <2>3. ASSUME NEW b \in Ballot
        PROVE  SafeAt(b, v)' =
                 \/ b = 0
                 \/ \E Q \in Quorum :
                      /\ \A a \in Q : maxBal'[a] \geq b
                      /\ \E c \in -1..(b-1) :
                           /\ (c # -1) => /\ SafeAt(c, v)'
                                          /\ \A a \in Q :
                                               \A w \in Value :
                                                  VotedFor(a, c, w)' => (w = v)
                           /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)'
    <3> HIDE DEF op, SA, SafeAt
    <3>0. b \in Nat
      BY DEF Ballot
    <3>1. SafeAt(b, v)' = SA[b]
      BY <2>1
    <3>2. SA[b] = op(SA, b)
      BY <2>2, <3>0
    <3>3a. \A c \in 0..(b-1) : SA[c] = SafeAt(c, v)'
      BY <2>1 DEF Ballot
    <3>3. \A c \in -1..(b-1) : (c # -1) => (SA[c] = SafeAt(c, v)')
      BY <3>3a, <3>0
    <3>4. op(SA, b) =
            \/ b = 0
            \/ \E Q \in Quorum :
                 /\ \A a \in Q : maxBal'[a] \geq b
                 /\ \E c \in -1..(b-1) :
                      /\ (c # -1) => /\ SafeAt(c, v)'
                                     /\ \A a \in Q :
                                          \A w \in Value :
                                             VotedFor(a, c, w)' => (w = v)
                      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)'
      BY <3>3 DEF op
    <3>5. QED
      BY <3>1, <3>2, <3>4
  <2>4. QED
    BY <2>3
<1>2. QED
  BY <1>1

-----------------------------------------------------------------------------

LEMMA SafeAtStable ==
  ASSUME TypeOK, NEW self \in Acceptor, NEW bal \in Ballot, BallotAction(self, bal)
  PROVE  \A b \in Ballot, v \in Value : SafeAt(b, v) => SafeAt(b, v)'
<1> USE DEF Ballot
<1>mono. \A a \in Acceptor : maxBal'[a] \in (Nat \cup {-1}) /\ maxBal'[a] >= maxBal[a]
  BY DEF BallotAction, IncreaseMaxBal, VoteFor, TypeOK
<1>self. maxBal[self] <= bal
  BY DEF BallotAction, IncreaseMaxBal, VoteFor, TypeOK
<1>veq. \A a \in Acceptor : a # self => votes'[a] = votes[a]
  BY DEF BallotAction, IncreaseMaxBal, VoteFor, TypeOK
<1>new. \A a \in Acceptor, e \in Ballot, w \in Value :
          (VotedFor(a, e, w)' /\ e # bal) => VotedFor(a, e, w)
  BY DEF BallotAction, IncreaseMaxBal, VoteFor, VotedFor, TypeOK
<1> DEFINE P(b) == \A v \in Value : SafeAt(b, v) => SafeAt(b, v)'
<1>ind. ASSUME NEW b \in Nat, \A cc \in 0..(b-1) : P(cc)
        PROVE  P(b)
  <2>ih. \A cc \in 0..(b-1) : P(cc)
    BY <1>ind
  <2>1. SUFFICES ASSUME NEW v \in Value, SafeAt(b, v)
                 PROVE  SafeAt(b, v)'
    BY DEF P
  <2>sb. SafeAt(b, v)
    BY <2>1
  <2>2. CASE b = 0
    BY <2>2, SafeAtPropPrime
  <2>3. CASE b # 0
    <3>1. \E Q \in Quorum :
            /\ \A a \in Q : maxBal[a] \geq b
            /\ \E c \in -1..(b-1) :
                 /\ (c # -1) => /\ SafeAt(c, v)
                                /\ \A a \in Q :
                                     \A w \in Value : VotedFor(a, c, w) => (w = v)
                 /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
      BY <2>sb, <2>3, SafeAtProp
    <3>2. PICK Q \in Quorum, c \in -1..(b-1) :
            /\ \A a \in Q : maxBal[a] \geq b
            /\ (c # -1) => /\ SafeAt(c, v)
                           /\ \A a \in Q :
                                \A w \in Value : VotedFor(a, c, w) => (w = v)
            /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
      BY <3>1
    <3>q. \A a \in Q : a \in Acceptor
      BY QA
    <3>mb. \A a \in Q : maxBal[a] \geq b
      BY <3>2
    <3>k. \A a \in Q, e \in 0..(b-1), w \in Value :
            VotedFor(a, e, w)' => VotedFor(a, e, w)
      <4>1. ASSUME NEW a \in Q, NEW e \in 0..(b-1), NEW w \in Value, VotedFor(a, e, w)'
            PROVE  VotedFor(a, e, w)
        <5>0. VotedFor(a, e, w)'
          BY <4>1
        <5>1. a \in Acceptor
          BY <3>q
        <5>2. CASE a = self
          <6>1. maxBal[self] \geq b
            BY <3>mb, <5>2
          <6>2. bal \geq b
            BY <6>1, <1>self, TypeOK DEF TypeOK
          <6>3. e # bal
            BY <6>2
          <6>4. QED
            BY <1>new, <5>0, <6>3, <5>1
        <5>3. CASE a # self
          <6>1. votes'[a] = votes[a]
            BY <1>veq, <5>1, <5>3
          <6>2. QED
            BY <5>0, <6>1 DEF VotedFor
        <5>4. QED
          BY <5>2, <5>3
      <4>2. QED
        BY <4>1
    <3>3. \A a \in Q : maxBal'[a] \geq b
      <4>1. ASSUME NEW a \in Q PROVE maxBal'[a] \geq b
        <5>1. a \in Acceptor
          BY <3>q
        <5>2. maxBal[a] \geq b
          BY <3>mb
        <5>3. maxBal'[a] \geq maxBal[a] /\ maxBal'[a] \in (Nat \cup {-1})
          BY <1>mono, <5>1
        <5>4. QED
          BY <5>2, <5>3, <5>1, TypeOK DEF TypeOK
      <4>2. QED
        BY <4>1
    <3>cv. (c # -1) => SafeAt(c, v)
      BY <3>2
    <3>cw. (c # -1) => \A a \in Q : \A w \in Value : VotedFor(a, c, w) => (w = v)
      BY <3>2
    <3>4. (c # -1) => /\ SafeAt(c, v)'
                      /\ \A a \in Q :
                           \A w \in Value : VotedFor(a, c, w)' => (w = v)
      <4>1. ASSUME c # -1
            PROVE  /\ SafeAt(c, v)'
                   /\ \A a \in Q :
                        \A w \in Value : VotedFor(a, c, w)' => (w = v)
        <5>1. c \in 0..(b-1)
          BY <4>1
        <5>2. SafeAt(c, v)
          BY <3>cv, <4>1
        <5>3. SafeAt(c, v)'
          BY <5>1, <5>2, <2>ih DEF P
        <5>4. \A a \in Q, w \in Value : VotedFor(a, c, w) => (w = v)
          BY <3>cw, <4>1
        <5>5. \A a \in Q, w \in Value : VotedFor(a, c, w)' => (w = v)
          BY <3>k, <5>1, <5>4
        <5>6. QED
          BY <5>3, <5>5
      <4>2. QED
        BY <4>1
    <3>dn. \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
      BY <3>2
    <3>5. \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)'
      <4>1. ASSUME NEW d \in (c+1)..(b-1), NEW a \in Q
            PROVE  DidNotVoteIn(a, d)'
        <5>1. d \in 0..(b-1)
          BY <3>2
        <5>2. DidNotVoteIn(a, d)
          BY <3>dn
        <5>3. \A w \in Value : VotedFor(a, d, w)' => VotedFor(a, d, w)
          BY <3>k, <5>1
        <5>4. QED
          BY <5>2, <5>3 DEF DidNotVoteIn
      <4>2. QED
        BY <4>1
    <3>6. SafeAt(b, v)' =
            \/ b = 0
            \/ \E QQ \in Quorum :
                 /\ \A a \in QQ : maxBal'[a] \geq b
                 /\ \E cc \in -1..(b-1) :
                      /\ (cc # -1) => /\ SafeAt(cc, v)'
                                      /\ \A a \in QQ :
                                           \A w \in Value : VotedFor(a, cc, w)' => (w = v)
                      /\ \A d \in (cc+1)..(b-1), a \in QQ : DidNotVoteIn(a, d)'
      BY SafeAtPropPrime
    <3>7. \E QQ \in Quorum :
            /\ \A a \in QQ : maxBal'[a] \geq b
            /\ \E cc \in -1..(b-1) :
                 /\ (cc # -1) => /\ SafeAt(cc, v)'
                                 /\ \A a \in QQ :
                                      \A w \in Value : VotedFor(a, cc, w)' => (w = v)
                 /\ \A d \in (cc+1)..(b-1), a \in QQ : DidNotVoteIn(a, d)'
      BY <3>2, <3>3, <3>4, <3>5
    <3>8. QED
      BY <3>6, <3>7
  <2>4. QED
    BY <2>2, <2>3
<1>2. \A b \in Nat : P(b)
  BY <1>ind, NI!GeneralNatInduction
<1>3. QED
  BY <1>2 DEF P

-----------------------------------------------------------------------------

LEMMA InductiveInvariance ==
  ASSUME VInv, [Next]_vars
  PROVE  VInv'
<1> USE DEF Ballot
<1>typ. TypeOK
  BY DEF VInv
<1>i2. VInv2
  BY DEF VInv
<1>i3. VInv3
  BY DEF VInv
<1>i4. VInv4
  BY DEF VInv
<1>next. Next \/ (vars' = vars)
  BY DEF vars
<1>1. CASE vars' = vars
  <2>1. votes' = votes /\ maxBal' = maxBal
    BY <1>1 DEF vars
  <2>su. \A b \in Ballot, v \in Value : SafeAt(b, v)' = SafeAt(b, v)
    BY <2>1 DEF SafeAt, VotedFor, DidNotVoteIn
  <2>tok. TypeOK'
    BY <1>typ, <2>1 DEF TypeOK
  <2>v2. VInv2'
    <3>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value, VotedFor(a, b, v)'
          PROVE  SafeAt(b, v)'
      <4>1. VotedFor(a, b, v)
        BY <3>1, <2>1 DEF VotedFor
      <4>2. SafeAt(b, v)
        BY <4>1, <1>i2 DEF VInv2
      <4>3. QED
        BY <4>2, <2>su
    <3>2. QED
      BY <3>1 DEF VInv2
  <2>v3. VInv3'
    BY <1>i3, <2>1 DEF VInv3, VotedFor
  <2>v4. VInv4'
    <3>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot, maxBal'[a] < b
          PROVE  DidNotVoteIn(a, b)'
      <4>1. maxBal[a] < b
        BY <3>1, <2>1
      <4>2. DidNotVoteIn(a, b)
        BY <4>1, <1>i4 DEF VInv4
      <4>3. QED
        BY <4>2, <2>1 DEF DidNotVoteIn, VotedFor
    <3>2. QED
      BY <3>1 DEF VInv4
  <2>2. QED
    BY <2>tok, <2>v2, <2>v3, <2>v4 DEF VInv
<1>2. CASE Next
  <2>0. PICK self \in Acceptor, bal \in Ballot : BallotAction(self, bal)
    BY <1>2, NextDef
  <2>stab. \A b \in Ballot, v \in Value : SafeAt(b, v) => SafeAt(b, v)'
    BY <1>typ, <2>0, SafeAtStable
  <2>mono. \A a \in Acceptor : maxBal'[a] \in (Nat \cup {-1}) /\ maxBal'[a] >= maxBal[a]
    BY <2>0, <1>typ DEF BallotAction, IncreaseMaxBal, VoteFor, TypeOK
  <2>self. maxBal'[self] = bal
    BY <2>0, <1>typ DEF BallotAction, IncreaseMaxBal, VoteFor, TypeOK
  <2>g. \A a \in Acceptor, b \in Ballot, w \in Value :
          VotedFor(a, b, w)' => (VotedFor(a, b, w) \/ (a = self /\ b = bal))
    BY <2>0, <1>typ DEF BallotAction, IncreaseMaxBal, VoteFor, VotedFor, TypeOK
  <2>nv. \A a \in Acceptor, b \in Ballot, vv \in Value :
           VotedFor(a, b, vv)' => (VotedFor(a, b, vv) \/ SafeAt(b, vv))
    <3>1. CASE IncreaseMaxBal(self, bal)
      BY <3>1 DEF IncreaseMaxBal, VotedFor
    <3>2. CASE \E vv0 \in Value : VoteFor(self, bal, vv0)
      <4>0. PICK vv0 \in Value : VoteFor(self, bal, vv0)
        BY <3>2
      <4>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW vv \in Value, VotedFor(a, b, vv)'
            PROVE  VotedFor(a, b, vv) \/ SafeAt(b, vv)
        <5>1. <<b, vv>> \in votes'[a]
          BY <4>1 DEF VotedFor
        <5>2. CASE a = self
          <6>1. <<b, vv>> \in votes[self] \cup {<<bal, vv0>>}
            BY <5>1, <4>0, <5>2, <1>typ DEF VoteFor, TypeOK
          <6>2. CASE <<b, vv>> \in votes[self]
            BY <6>2, <5>2 DEF VotedFor
          <6>3. CASE <<b, vv>> = <<bal, vv0>>
            <7>1. SafeAt(bal, vv0)
              BY <4>0 DEF VoteFor
            <7>2. b = bal /\ vv = vv0
              BY <6>3
            <7>3. QED
              BY <7>1, <7>2
          <6>4. QED
            BY <6>1, <6>2, <6>3
        <5>3. CASE a # self
          <6>1. votes'[a] = votes[a]
            BY <4>0, <5>3, <1>typ DEF VoteFor, TypeOK
          <6>2. QED
            BY <5>1, <6>1 DEF VotedFor
        <5>4. QED
          BY <5>2, <5>3
      <4>2. QED
        BY <4>1
    <3>3. QED
      BY <2>0, <3>1, <3>2 DEF BallotAction
  <2>tok. TypeOK'
    BY <2>0, <1>typ DEF BallotAction, IncreaseMaxBal, VoteFor, TypeOK
  <2>v2. VInv2'
    <3>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW vv \in Value, VotedFor(a, b, vv)'
          PROVE  SafeAt(b, vv)'
      <4>1. VotedFor(a, b, vv) \/ SafeAt(b, vv)
        BY <2>nv, <3>1
      <4>2. SafeAt(b, vv)
        BY <4>1, <1>i2 DEF VInv2
      <4>3. QED
        BY <4>2, <2>stab
    <3>2. QED
      BY <3>1 DEF VInv2
  <2>v3. VInv3'
    <3>1. CASE IncreaseMaxBal(self, bal)
      BY <3>1, <1>i3 DEF IncreaseMaxBal, VInv3, VotedFor
    <3>2. CASE \E vv0 \in Value : VoteFor(self, bal, vv0)
      <4>0. PICK vv0 \in Value : VoteFor(self, bal, vv0)
        BY <3>2
      <4>uni. \A a \in Acceptor, w \in Value : VotedFor(a, bal, w)' => (w = vv0)
        <5>1. ASSUME NEW a \in Acceptor, NEW w \in Value, VotedFor(a, bal, w)'
              PROVE  w = vv0
          <6>1. CASE a = self
            <7>1. <<bal, w>> \in votes[self] \cup {<<bal, vv0>>}
              BY <5>1, <4>0, <6>1, <1>typ DEF VoteFor, VotedFor, TypeOK
            <7>2. ~ (<<bal, w>> \in votes[self])
              BY <4>0, <6>1, <5>1 DEF VoteFor, DidNotVoteIn, VotedFor
            <7>3. QED
              BY <7>1, <7>2
          <6>2. CASE a # self
            <7>1. VotedFor(a, bal, w)
              BY <5>1, <4>0, <6>2, <1>typ DEF VoteFor, VotedFor, TypeOK
            <7>2. QED
              BY <7>1, <4>0, <6>2 DEF VoteFor
          <6>3. QED
            BY <6>1, <6>2
        <5>2. QED
          BY <5>1
      <4>1. ASSUME NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW b \in Ballot,
                   NEW v1 \in Value, NEW v2 \in Value,
                   VotedFor(a1, b, v1)', VotedFor(a2, b, v2)'
            PROVE  v1 = v2
        <5>1. CASE b = bal
          <6>1. v1 = vv0
            BY <4>uni, <4>1, <5>1
          <6>2. v2 = vv0
            BY <4>uni, <4>1, <5>1
          <6>3. QED
            BY <6>1, <6>2
        <5>2. CASE b # bal
          <6>1. VotedFor(a1, b, v1)
            BY <2>g, <4>1, <5>2
          <6>2. VotedFor(a2, b, v2)
            BY <2>g, <4>1, <5>2
          <6>3. QED
            BY <6>1, <6>2, <1>i3 DEF VInv3
        <5>3. QED
          BY <5>1, <5>2
      <4>2. QED
        BY <4>1 DEF VInv3
    <3>3. QED
      BY <2>0, <3>1, <3>2 DEF BallotAction
  <2>v4. VInv4'
    <3>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot, maxBal'[a] < b
          PROVE  DidNotVoteIn(a, b)'
      <4>1. maxBal[a] < b
        BY <3>1, <2>mono, <1>typ DEF TypeOK
      <4>2. DidNotVoteIn(a, b)
        BY <4>1, <1>i4 DEF VInv4
      <4>3. ASSUME NEW w \in Value, VotedFor(a, b, w)'
            PROVE  FALSE
        <5>1. VotedFor(a, b, w) \/ (a = self /\ b = bal)
          BY <2>g, <4>3
        <5>2. CASE VotedFor(a, b, w)
          BY <5>2, <4>2 DEF DidNotVoteIn
        <5>3. CASE a = self /\ b = bal
          <6>1. maxBal'[a] = bal
            BY <2>self, <5>3
          <6>2. QED
            BY <6>1, <5>3, <3>1
        <5>4. QED
          BY <5>1, <5>2, <5>3
      <4>4. QED
        BY <4>3 DEF DidNotVoteIn
    <3>2. QED
      BY <3>1 DEF VInv4
  <2>qed. QED
    BY <2>tok, <2>v2, <2>v3, <2>v4 DEF VInv
<1>3. QED
  BY <1>1, <1>2, <1>next

-----------------------------------------------------------------------------

LEMMA InitImpliesInv ==
  ASSUME Init
  PROVE  VInv
<1> USE DEF Ballot
<1>1. votes = [a \in Acceptor |-> {}]
  BY DEF Init
<1>2. maxBal = [a \in Acceptor |-> -1]
  BY DEF Init
<1>tok. TypeOK
  BY <1>1, <1>2 DEF TypeOK
<1>nv. \A a \in Acceptor, b \in Ballot, v \in Value : ~ VotedFor(a, b, v)
  BY <1>1 DEF VotedFor
<1>v2. VInv2
  BY <1>nv DEF VInv2
<1>v3. VInv3
  BY <1>nv DEF VInv3
<1>v4. VInv4
  BY <1>nv DEF VInv4, DidNotVoteIn
<1>qed. QED
  BY <1>tok, <1>v2, <1>v3, <1>v4 DEF VInv

-----------------------------------------------------------------------------

THEOREM VT2 == Spec => []VInv
<1>1. Init => VInv
  BY InitImpliesInv
<1>2. VInv /\ [Next]_vars => VInv'
  BY InductiveInvariance
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

ASSUME AcceptorFinite == IsFiniteSet(Acceptor)

ASSUME ValueNonempty == Value # {}
-----------------------------------------------------------------------------

AXIOM SubsetOfFiniteSetFinite == 
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

AXIOM FiniteSetHasMax == 
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

AXIOM IntervalFinite == \A i, j \in Int : IsFiniteSet(i..j)
-----------------------------------------------------------------------------

-------------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

===============================================================================

