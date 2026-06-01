----------------------------- MODULE VoteProof_VT3 ------------------------------

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

ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}
-----------------------------------------------------------------------------

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

ASSUME AcceptorNonempty == Acceptor # {}

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

C == INSTANCE Consensus 

LOCAL INSTANCE NaturalsInduction

SafeAtBody(SA, bb, v) ==
   \/ bb = 0
   \/ \E Q \in Quorum :
        /\ \A a \in Q : maxBal[a] \geq bb
        /\ \E c \in -1..(bb-1) :
             /\ (c # -1) => /\ SA[c]
                            /\ \A a \in Q : \A w \in Value : VotedFor(a,c,w) => (w = v)
             /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a,d)

\* State-parametric version of the SafeAt body: MB plays the role of maxBal,
\* VT the role of votes.  Its definition mentions no state variable, so
\* (GSafeAt(maxBal,votes,b,v))' = GSafeAt(maxBal',votes',b,v) by argument priming.
GBody(MB, VT, SA, bb, v) ==
   \/ bb = 0
   \/ \E Q \in Quorum :
        /\ \A a \in Q : MB[a] \geq bb
        /\ \E c \in -1..(bb-1) :
             /\ (c # -1) => /\ SA[c]
                            /\ \A a \in Q : \A w \in Value : (<<c, w>> \in VT[a]) => (w = v)
             /\ \A d \in (c+1)..(bb-1), a \in Q : \A w \in Value : <<d, w>> \notin VT[a]

GSafeAt(MB, VT, b, v) ==
   LET SA[bb \in Ballot] == GBody(MB, VT, SA, bb, v)
   IN  SA[b]

GChosenIn(VT, b, v) == \E Q \in Quorum : \A a \in Q : <<b, v>> \in VT[a]

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
<1>1. ASSUME NEW Q \in Quorum PROVE Q # {}
   <2>1. Q \cap Q # {}
      BY <1>1, QA
   <2>2. QED
      BY <2>1
<1>2. QED BY <1>1

LEMMA SafeAtDef ==
  ASSUME NEW b \in Ballot, NEW v \in Value
  PROVE  SafeAt(b, v) = SafeAtBody([bb \in Ballot |-> SafeAt(bb, v)], b, v)
<1> DEFINE Def(g, n) == SafeAtBody(g, n, v)
           SA[bb \in Nat] == Def(SA, bb)
<1>1. ASSUME NEW mm \in Nat, NEW gg, NEW hh, \A i \in 0..(mm-1) : gg[i] = hh[i]
      PROVE  Def(gg, mm) = Def(hh, mm)
   <2>0. \A c \in 0..(mm-1) : gg[c] = hh[c]
      BY <1>1
   <2>1. SafeAtBody(gg, mm, v) = SafeAtBody(hh, mm, v)
      BY <1>1, <2>0 DEF SafeAtBody
   <2>2. QED
      BY <2>1 DEF Def
<1>2. \A bb \in Nat : SA[bb] = SafeAt(bb, v)
   BY DEF SafeAt, SafeAtBody, Def, Ballot
<1> HIDE DEF Def
<1>3. SA = [bb \in Nat |-> Def(SA, bb)]
   BY <1>1, RecursiveFcnOfNat, Isa
<1> USE DEF Def
<1>4. SA[b] = SafeAtBody(SA, b, v)
   BY <1>3 DEF Def, Ballot
<1>5. SA = [bb \in Ballot |-> SafeAt(bb, v)]
   BY <1>2, <1>3 DEF Ballot
<1>6. QED
   BY <1>2, <1>4, <1>5 DEF Ballot

LEMMA SafeAtUnfold ==
  ASSUME NEW b \in Ballot, NEW v \in Value
  PROVE  SafeAt(b, v) <=>
           \/ b = 0
           \/ \E Q \in Quorum :
                /\ \A a \in Q : maxBal[a] \geq b
                /\ \E c \in -1..(b-1) :
                     /\ (c # -1) => /\ SafeAt(c, v)
                                    /\ \A a \in Q : \A w \in Value :
                                          VotedFor(a, c, w) => (w = v)
                     /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
<1>1. SafeAt(b, v) = SafeAtBody([bb \in Ballot |-> SafeAt(bb, v)], b, v)
   BY SafeAtDef
<1>2. \A c \in 0..(b-1) : [bb \in Ballot |-> SafeAt(bb, v)][c] = SafeAt(c, v)
   BY DEF Ballot
<1>3. QED
   BY <1>1, <1>2 DEF SafeAtBody

LEMMA GSafeAtDef ==
  ASSUME NEW MB, NEW VT, NEW b \in Ballot, NEW v \in Value
  PROVE  GSafeAt(MB, VT, b, v) =
            GBody(MB, VT, [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)], b, v)
<1> DEFINE Def(g, n) == GBody(MB, VT, g, n, v)
           SA[bb \in Nat] == Def(SA, bb)
<1>1. ASSUME NEW mm \in Nat, NEW gg, NEW hh, \A i \in 0..(mm-1) : gg[i] = hh[i]
      PROVE  Def(gg, mm) = Def(hh, mm)
   <2>0. \A c \in 0..(mm-1) : gg[c] = hh[c]
      BY <1>1
   <2>1. GBody(MB, VT, gg, mm, v) = GBody(MB, VT, hh, mm, v)
      BY <1>1, <2>0 DEF GBody
   <2>2. QED
      BY <2>1 DEF Def
<1>2. \A bb \in Nat : SA[bb] = GSafeAt(MB, VT, bb, v)
   BY DEF GSafeAt, GBody, Def, Ballot
<1> HIDE DEF Def
<1>3. SA = [bb \in Nat |-> Def(SA, bb)]
   BY <1>1, RecursiveFcnOfNat, Isa
<1> USE DEF Def
<1>4. SA[b] = GBody(MB, VT, SA, b, v)
   BY <1>3 DEF Def, Ballot
<1>5. SA = [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)]
   BY <1>2, <1>3 DEF Ballot
<1>6. QED
   BY <1>2, <1>4, <1>5 DEF Ballot

LEMMA GSafeAtUnfold ==
  ASSUME NEW MB, NEW VT, NEW b \in Ballot, NEW v \in Value
  PROVE  GSafeAt(MB, VT, b, v) <=>
           \/ b = 0
           \/ \E Q \in Quorum :
                /\ \A a \in Q : MB[a] \geq b
                /\ \E c \in -1..(b-1) :
                     /\ (c # -1) => /\ GSafeAt(MB, VT, c, v)
                                    /\ \A a \in Q : \A w \in Value :
                                          (<<c, w>> \in VT[a]) => (w = v)
                     /\ \A d \in (c+1)..(b-1), a \in Q : \A w \in Value :
                           <<d, w>> \notin VT[a]
<1>1. GSafeAt(MB, VT, b, v) =
         GBody(MB, VT, [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)], b, v)
   BY GSafeAtDef
<1>2. \A c \in 0..(b-1) : [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)][c] = GSafeAt(MB, VT, c, v)
   BY DEF Ballot
<1>3. QED
   BY <1>1, <1>2 DEF GBody

LEMMA SafeAtIsG ==
  ASSUME NEW b \in Ballot, NEW v \in Value
  PROVE  SafeAt(b, v) = GSafeAt(maxBal, votes, b, v)
BY DEF SafeAt, GSafeAt, SafeAtBody, GBody, VotedFor, DidNotVoteIn

LEMMA SafeAtIsGPrime ==
  ASSUME NEW b \in Ballot, NEW v \in Value
  PROVE  SafeAt(b, v)' = GSafeAt(maxBal', votes', b, v)
BY DEF SafeAt, GSafeAt, SafeAtBody, GBody, VotedFor, DidNotVoteIn

LEMMA GSafeStable ==
  ASSUME NEW MB, NEW VT, NEW MB2, NEW VT2,
         \A a \in Acceptor : MB[a] \in Int,
         \A a \in Acceptor : MB2[a] \in Int,
         \A a \in Acceptor : MB[a] \leq MB2[a],
         \A a \in Acceptor, e \in Ballot, w \in Value :
            (<<e, w>> \in VT2[a]) => (<<e, w>> \in VT[a] \/ MB[a] \leq e)
  PROVE  \A b \in Ballot, v \in Value :
            GSafeAt(MB, VT, b, v) => GSafeAt(MB2, VT2, b, v)
<1> DEFINE P(bb) == \A vv \in Value :
                       GSafeAt(MB, VT, bb, vv) => GSafeAt(MB2, VT2, bb, vv)
<1>1. \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
   <2> SUFFICES ASSUME NEW n \in Nat, \A m \in 0..(n-1) : P(m)
               PROVE  P(n)
      OBVIOUS
   <2> SUFFICES ASSUME NEW v \in Value, GSafeAt(MB, VT, n, v)
               PROVE  GSafeAt(MB2, VT2, n, v)
      BY DEF P
   <2>1. CASE n = 0
      BY <2>1, GSafeAtUnfold DEF Ballot
   <2>2. CASE n # 0
      <3>1. \E Q \in Quorum :
               /\ \A a \in Q : MB[a] \geq n
               /\ \E c \in -1..(n-1) :
                    /\ (c # -1) => /\ GSafeAt(MB, VT, c, v)
                                   /\ \A a \in Q : \A w \in Value :
                                         (<<c, w>> \in VT[a]) => (w = v)
                    /\ \A d \in (c+1)..(n-1), a \in Q : \A w \in Value : <<d, w>> \notin VT[a]
         <4>1. GSafeAt(MB, VT, n, v) =
                  GBody(MB, VT, [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)], n, v)
            BY GSafeAtDef DEF Ballot
         <4>2. \A c \in 0..(n-1) :
                  [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)][c] = GSafeAt(MB, VT, c, v)
            BY DEF Ballot
         <4>3. GBody(MB, VT, [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)], n, v)
            BY <4>1
         <4>4. QED
            BY <2>2, <4>2, <4>3 DEF GBody
      <3>2. PICK Q \in Quorum :
               /\ \A a \in Q : MB[a] \geq n
               /\ \E c \in -1..(n-1) :
                    /\ (c # -1) => /\ GSafeAt(MB, VT, c, v)
                                   /\ \A a \in Q : \A w \in Value :
                                         (<<c, w>> \in VT[a]) => (w = v)
                    /\ \A d \in (c+1)..(n-1), a \in Q : \A w \in Value : <<d, w>> \notin VT[a]
         BY <3>1
      <3>3. PICK c \in -1..(n-1) :
               /\ (c # -1) => /\ GSafeAt(MB, VT, c, v)
                              /\ \A a \in Q : \A w \in Value : (<<c, w>> \in VT[a]) => (w = v)
               /\ \A d \in (c+1)..(n-1), a \in Q : \A w \in Value : <<d, w>> \notin VT[a]
         BY <3>2
      <3>4. \A a \in Q : a \in Acceptor
         BY <3>2, QA
      <3>5. \A a \in Q : MB2[a] \geq n
         BY <3>2, <3>4
      <3>6. (c # -1) => /\ GSafeAt(MB2, VT2, c, v)
                        /\ \A a \in Q : \A w \in Value : (<<c, w>> \in VT2[a]) => (w = v)
         <4> SUFFICES ASSUME c # -1 PROVE
                /\ GSafeAt(MB2, VT2, c, v)
                /\ \A a \in Q : \A w \in Value : (<<c, w>> \in VT2[a]) => (w = v)
            OBVIOUS
         <4>0. c \in 0..(n-1)
            BY <3>3
         <4>1. /\ GSafeAt(MB, VT, c, v)
               /\ \A a \in Q : \A w \in Value : (<<c, w>> \in VT[a]) => (w = v)
            BY <3>3
         <4>2. GSafeAt(MB2, VT2, c, v)
            <5>1. P(c)
               BY <4>0
            <5>2. QED
               BY <4>1, <5>1 DEF P
         <4>3. \A a \in Q : \A w \in Value : (<<c, w>> \in VT2[a]) => (w = v)
            <5>1. ASSUME NEW a \in Q, NEW w \in Value, <<c, w>> \in VT2[a]
                  PROVE  w = v
               <6>1. a \in Acceptor
                  BY <3>4, <5>1
               <6>2. MB[a] \geq n
                  BY <3>2, <5>1
               <6>3. ~(MB[a] \leq c)
                  BY <4>0, <6>1, <6>2
               <6>4. c \in Ballot
                  BY <4>0 DEF Ballot
               <6>5. <<c, w>> \in VT[a]
                  BY <5>1, <6>1, <6>3, <6>4
               <6>6. QED
                  BY <4>1, <5>1, <6>5
            <5>2. QED
               BY <5>1
         <4>4. QED
            BY <4>2, <4>3
      <3>7. \A d \in (c+1)..(n-1), a \in Q : \A w \in Value : <<d, w>> \notin VT2[a]
         <4>1. ASSUME NEW d \in (c+1)..(n-1), NEW a \in Q, NEW w \in Value
               PROVE  <<d, w>> \notin VT2[a]
            <5>1. a \in Acceptor
               BY <3>4, <4>1
            <5>2. MB[a] \geq n
               BY <3>2, <4>1
            <5>3. ~(MB[a] \leq d)
               BY <4>1, <5>1, <5>2
            <5>4. <<d, w>> \notin VT[a]
               BY <3>3, <4>1
            <5>5. d \in Ballot
               BY <4>1 DEF Ballot
            <5>6. QED
               BY <4>1, <5>1, <5>3, <5>4, <5>5
         <4>2. QED
            BY <4>1
      <3>8. \E QQ \in Quorum :
               /\ \A a \in QQ : MB2[a] \geq n
               /\ \E cc \in -1..(n-1) :
                    /\ (cc # -1) => /\ GSafeAt(MB2, VT2, cc, v)
                                    /\ \A a \in QQ : \A w \in Value :
                                          (<<cc, w>> \in VT2[a]) => (w = v)
                    /\ \A d \in (cc+1)..(n-1), a \in QQ : \A w \in Value : <<d, w>> \notin VT2[a]
         BY <3>2, <3>3, <3>5, <3>6, <3>7
      <3>9. QED
         BY <2>2, <3>8, GSafeAtUnfold DEF Ballot
   <2>3. QED
      BY <2>1, <2>2
<1> HIDE DEF P
<1>2. \A n \in Nat : P(n)
   <2> DEFINE f == [k \in Nat |-> \A m \in 0..k : P(m)]
   <2>1. \A k \in Nat : f[k] = (\A m \in 0..k : P(m))
      BY DEF f
   <2>2. f[0]
      BY <1>1, <2>1
   <2>3. \A k \in Nat : f[k] => f[k+1]
      <3>1. ASSUME NEW k \in Nat, f[k] PROVE f[k+1]
         <4>1. \A m \in 0..k : P(m)
            BY <3>1, <2>1
         <4>2. P(k+1)
            BY <1>1, <4>1
         <4>3. \A m \in 0..(k+1) : P(m)
            BY <4>1, <4>2
         <4>4. QED
            BY <4>3, <2>1
      <3>2. QED BY <3>1
   <2>4. \A k \in Nat : f[k]
      BY <2>2, <2>3, SimpleNatInduction
   <2>5. QED
      BY <2>4, <2>1
<1>3. QED
   BY <1>2 DEF P, Ballot

LEMMA GSafeSound ==
  ASSUME NEW MB, NEW VT
  PROVE  \A b \in Ballot : \A v \in Value :
            GSafeAt(MB, VT, b, v) =>
               \A c \in 0..(b-1) : \A w \in Value : GChosenIn(VT, c, w) => (w = v)
<1> DEFINE P(bb) == \A vv \in Value :
                       GSafeAt(MB, VT, bb, vv) =>
                          \A cc \in 0..(bb-1) : \A ww \in Value :
                             GChosenIn(VT, cc, ww) => (ww = vv)
<1>1. \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
   <2> SUFFICES ASSUME NEW n \in Nat, \A m \in 0..(n-1) : P(m)
               PROVE  P(n)
      OBVIOUS
   <2> SUFFICES ASSUME NEW v \in Value, GSafeAt(MB, VT, n, v),
                       NEW c \in 0..(n-1), NEW w \in Value, GChosenIn(VT, c, w)
               PROVE  w = v
      BY DEF P
   <2>1. n # 0
      OBVIOUS
   <2>2. \E Q \in Quorum :
            /\ \A a \in Q : MB[a] \geq n
            /\ \E cc \in -1..(n-1) :
                 /\ (cc # -1) => /\ GSafeAt(MB, VT, cc, v)
                                 /\ \A a \in Q : \A ww \in Value :
                                       (<<cc, ww>> \in VT[a]) => (ww = v)
                 /\ \A d \in (cc+1)..(n-1), a \in Q : \A ww \in Value : <<d, ww>> \notin VT[a]
      <3>1. GSafeAt(MB, VT, n, v) =
               GBody(MB, VT, [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)], n, v)
         BY GSafeAtDef DEF Ballot
      <3>2. \A cc \in 0..(n-1) :
               [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)][cc] = GSafeAt(MB, VT, cc, v)
         BY DEF Ballot
      <3>3. GBody(MB, VT, [bb \in Ballot |-> GSafeAt(MB, VT, bb, v)], n, v)
         BY <3>1
      <3>4. QED
         BY <2>1, <3>2, <3>3 DEF GBody
   <2>3. PICK Q \in Quorum :
            /\ \A a \in Q : MB[a] \geq n
            /\ \E cc \in -1..(n-1) :
                 /\ (cc # -1) => /\ GSafeAt(MB, VT, cc, v)
                                 /\ \A a \in Q : \A ww \in Value :
                                       (<<cc, ww>> \in VT[a]) => (ww = v)
                 /\ \A d \in (cc+1)..(n-1), a \in Q : \A ww \in Value : <<d, ww>> \notin VT[a]
      BY <2>2
   <2>4. PICK cc \in -1..(n-1) :
            /\ (cc # -1) => /\ GSafeAt(MB, VT, cc, v)
                            /\ \A a \in Q : \A ww \in Value :
                                  (<<cc, ww>> \in VT[a]) => (ww = v)
            /\ \A d \in (cc+1)..(n-1), a \in Q : \A ww \in Value : <<d, ww>> \notin VT[a]
      BY <2>3
   <2>5. PICK Qc \in Quorum : \A a \in Qc : <<c, w>> \in VT[a]
      BY DEF GChosenIn
   <2>6. \E a \in Q : a \in Qc
      BY <2>3, <2>5, QA
   <2>7. PICK astar \in Q : astar \in Qc
      BY <2>6
   <2>8. <<c, w>> \in VT[astar]
      BY <2>5, <2>7
   <2>9. ~(c \in (cc+1)..(n-1))
      <3>1. ASSUME c \in (cc+1)..(n-1) PROVE FALSE
         <4>1. <<c, w>> \notin VT[astar]
            BY <2>4, <2>7, <3>1
         <4>2. QED
            BY <4>1, <2>8
      <3>2. QED BY <3>1
   <2>10. c \leq cc
      BY <2>4, <2>9
   <2>11. cc # -1
      BY <2>10
   <2>12. /\ GSafeAt(MB, VT, cc, v)
          /\ \A a \in Q : \A ww \in Value : (<<cc, ww>> \in VT[a]) => (ww = v)
      BY <2>4, <2>11
   <2>13. CASE c = cc
      BY <2>7, <2>8, <2>12, <2>13
   <2>14. CASE c < cc
      <3>1. cc \in 0..(n-1)
         BY <2>4, <2>11
      <3>2. P(cc)
         BY <3>1
      <3>3. GSafeAt(MB, VT, cc, v) =>
               \A c1 \in 0..(cc-1) : \A ww \in Value : GChosenIn(VT, c1, ww) => (ww = v)
         BY <3>2 DEF P
      <3>4. c \in 0..(cc-1)
         BY <2>14
      <3>5. GChosenIn(VT, c, w)
         BY <2>5 DEF GChosenIn
      <3>6. QED
         BY <2>12, <3>3, <3>4, <3>5
   <2>15. QED
      BY <2>10, <2>13, <2>14
<1> HIDE DEF P
<1>2. \A n \in Nat : P(n)
   <2> DEFINE f == [k \in Nat |-> \A m \in 0..k : P(m)]
   <2>1. \A k \in Nat : f[k] = (\A m \in 0..k : P(m))
      BY DEF f
   <2>2. f[0]
      BY <1>1, <2>1
   <2>3. \A k \in Nat : f[k] => f[k+1]
      <3>1. ASSUME NEW k \in Nat, f[k] PROVE f[k+1]
         <4>1. \A m \in 0..k : P(m)
            BY <3>1, <2>1
         <4>2. P(k+1)
            BY <1>1, <4>1
         <4>3. \A m \in 0..(k+1) : P(m)
            BY <4>1, <4>2
         <4>4. QED
            BY <4>3, <2>1
      <3>2. QED BY <3>1
   <2>4. \A k \in Nat : f[k]
      BY <2>2, <2>3, SimpleNatInduction
   <2>5. QED
      BY <2>4, <2>1
<1>3. QED
   BY <1>2 DEF Ballot, P

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

OneValuePerBallot ==
  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                VotedFor(a, b, v) => SafeAt(b, v)

NotVotedAbove == \A a \in Acceptor, b \in Ballot :
                    maxBal[a] < b => DidNotVoteIn(a, b)

Inv == /\ TypeOK
       /\ OneValuePerBallot
       /\ VotesSafe
       /\ NotVotedAbove

LEMMA NextProps ==
  ASSUME TypeOK, Next
  PROVE  /\ \A a \in Acceptor : maxBal'[a] \in Int
         /\ \A a \in Acceptor : maxBal[a] \leq maxBal'[a]
         /\ \A a \in Acceptor, e \in Ballot, w \in Value :
               (<<e, w>> \in votes'[a]) =>
                  (<<e, w>> \in votes[a] \/ maxBal[a] \leq e)
<1>0. \A a \in Acceptor : maxBal[a] \in Int
   BY DEF TypeOK, Ballot
<1>1. PICK self \in Acceptor : acceptor(self)
   BY DEF Next
<1>2. PICK b \in Ballot :
         \/ /\ b > maxBal[self]
            /\ maxBal' = [maxBal EXCEPT ![self] = b]
            /\ UNCHANGED votes
         \/ /\ \E v \in Value :
                 /\ /\ maxBal[self] \leq b
                    /\ DidNotVoteIn(self, b)
                    /\ \A p \in Acceptor \ {self} :
                          \A w \in Value : VotedFor(p, b, w) => (w = v)
                    /\ SafeAt(b, v)
                 /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                 /\ maxBal' = [maxBal EXCEPT ![self] = b]
   BY <1>1 DEF acceptor
<1>3. b \in Int /\ b \geq 0
   BY <1>2 DEF Ballot
<1>4. self \in Acceptor
   BY <1>1
<1>5. CASE /\ b > maxBal[self]
           /\ maxBal' = [maxBal EXCEPT ![self] = b]
           /\ UNCHANGED votes
   <2>1. \A a \in Acceptor : maxBal'[a] = (IF a = self THEN b ELSE maxBal[a])
      BY <1>5, <1>4 DEF TypeOK
   <2>2. \A a \in Acceptor : maxBal'[a] \in Int
      BY <2>1, <1>0, <1>3
   <2>3. \A a \in Acceptor : maxBal[a] \leq maxBal'[a]
      BY <2>1, <1>0, <1>3, <1>5
   <2>4. \A a \in Acceptor, e \in Ballot, w \in Value :
            (<<e, w>> \in votes'[a]) => (<<e, w>> \in votes[a] \/ maxBal[a] \leq e)
      BY <1>5
   <2>5. QED
      BY <2>2, <2>3, <2>4
<1>6. CASE \E v \in Value :
              /\ /\ maxBal[self] \leq b
                 /\ DidNotVoteIn(self, b)
                 /\ \A p \in Acceptor \ {self} :
                       \A w \in Value : VotedFor(p, b, w) => (w = v)
                 /\ SafeAt(b, v)
              /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
              /\ maxBal' = [maxBal EXCEPT ![self] = b]
   <2>1. PICK v \in Value :
            /\ maxBal[self] \leq b
            /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
            /\ maxBal' = [maxBal EXCEPT ![self] = b]
      BY <1>6
   <2>2. \A a \in Acceptor : maxBal'[a] = (IF a = self THEN b ELSE maxBal[a])
      BY <2>1, <1>4 DEF TypeOK
   <2>3. \A a \in Acceptor : maxBal'[a] \in Int
      BY <2>2, <1>0, <1>3
   <2>4. \A a \in Acceptor : maxBal[a] \leq maxBal'[a]
      BY <2>2, <2>1, <1>0, <1>3
   <2>5. \A a \in Acceptor : votes'[a] = (IF a = self THEN votes[a] \cup {<<b, v>>} ELSE votes[a])
      BY <2>1, <1>4 DEF TypeOK
   <2>6. \A a \in Acceptor, e \in Ballot, w \in Value :
            (<<e, w>> \in votes'[a]) => (<<e, w>> \in votes[a] \/ maxBal[a] \leq e)
      <3>1. ASSUME NEW a \in Acceptor, NEW e \in Ballot, NEW w \in Value,
                   <<e, w>> \in votes'[a]
            PROVE  <<e, w>> \in votes[a] \/ maxBal[a] \leq e
         <4>1. CASE a = self
            <5>1. <<e, w>> \in votes[a] \cup {<<b, v>>}
               BY <2>5, <3>1, <4>1
            <5>2. CASE <<e, w>> = <<b, v>>
               <6>1. e = b
                  BY <5>2
               <6>2. maxBal[a] \leq e
                  BY <6>1, <2>1, <4>1
               <6>3. QED BY <6>2
            <5>3. CASE <<e, w>> # <<b, v>>
               BY <5>1, <5>3
            <5>4. QED BY <5>2, <5>3
         <4>2. CASE a # self
            BY <2>5, <3>1, <4>2
         <4>3. QED BY <4>1, <4>2
      <3>2. QED BY <3>1
   <2>7. QED
      BY <2>3, <2>4, <2>6
<1>7. QED
   BY <1>2, <1>5, <1>6

LEMMA SafeAtStable ==
  ASSUME TypeOK, Next,
         NEW b \in Ballot, NEW v \in Value, SafeAt(b, v)
  PROVE  SafeAt(b, v)'
<1>1. \A a \in Acceptor : maxBal[a] \in Int
   BY DEF TypeOK, Ballot
<1>2. /\ \A a \in Acceptor : maxBal'[a] \in Int
      /\ \A a \in Acceptor : maxBal[a] \leq maxBal'[a]
      /\ \A a \in Acceptor, e \in Ballot, w \in Value :
            (<<e, w>> \in votes'[a]) => (<<e, w>> \in votes[a] \/ maxBal[a] \leq e)
   BY NextProps
<1>3. \A bb \in Ballot, vv \in Value :
         GSafeAt(maxBal, votes, bb, vv) => GSafeAt(maxBal', votes', bb, vv)
   BY <1>1, <1>2, GSafeStable
<1>4. GSafeAt(maxBal, votes, b, v)
   BY SafeAtIsG
<1>5. GSafeAt(maxBal', votes', b, v)
   BY <1>3, <1>4
<1>6. QED
   BY <1>5, SafeAtIsGPrime

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv
   OBVIOUS
<1>1. TypeOK
   BY DEF Init, TypeOK
<1>2. OneValuePerBallot
   BY DEF Init, OneValuePerBallot, VotedFor
<1>3. VotesSafe
   BY DEF Init, VotesSafe, VotedFor
<1>4. NotVotedAbove
   BY DEF Init, NotVotedAbove, VotedFor, DidNotVoteIn
<1>5. QED
   BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA InvInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
   OBVIOUS
<1> USE DEF Inv
<1>1. CASE vars' = vars
   <2>1. votes' = votes /\ maxBal' = maxBal
      BY <1>1 DEF vars
   <2>2. \A a \in Acceptor, bb \in Ballot, vv \in Value :
            VotedFor(a, bb, vv)' <=> VotedFor(a, bb, vv)
      BY <2>1 DEF VotedFor
   <2>3. \A a \in Acceptor, bb \in Ballot : DidNotVoteIn(a, bb)' <=> DidNotVoteIn(a, bb)
      BY <2>2 DEF DidNotVoteIn
   <2>4. \A bb \in Ballot, vv \in Value : SafeAt(bb, vv)' <=> SafeAt(bb, vv)
      <3>1. \A bb \in Ballot, vv \in Value : SafeAt(bb, vv)' = GSafeAt(maxBal, votes, bb, vv)
         BY <2>1, SafeAtIsGPrime
      <3>2. \A bb \in Ballot, vv \in Value : SafeAt(bb, vv) = GSafeAt(maxBal, votes, bb, vv)
         BY SafeAtIsG
      <3>3. QED BY <3>1, <3>2
   <2>5. TypeOK'
      BY <2>1 DEF TypeOK
   <2>6. OneValuePerBallot'
      BY <2>2 DEF OneValuePerBallot
   <2>7. VotesSafe'
      BY <2>2, <2>4 DEF VotesSafe
   <2>8. NotVotedAbove'
      BY <2>1, <2>3 DEF NotVotedAbove
   <2>9. QED
      BY <2>5, <2>6, <2>7, <2>8 DEF Inv
<1>2. CASE Next
   <2>1. PICK self \in Acceptor : acceptor(self)
      BY <1>2 DEF Next
   <2>2. PICK b \in Ballot :
            \/ /\ b > maxBal[self]
               /\ maxBal' = [maxBal EXCEPT ![self] = b]
               /\ UNCHANGED votes
            \/ /\ \E v \in Value :
                    /\ /\ maxBal[self] \leq b
                       /\ DidNotVoteIn(self, b)
                       /\ \A p \in Acceptor \ {self} :
                             \A w \in Value : VotedFor(p, b, w) => (w = v)
                       /\ SafeAt(b, v)
                    /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                    /\ maxBal' = [maxBal EXCEPT ![self] = b]
      BY <2>1 DEF acceptor
   <2>3. self \in Acceptor /\ b \in Ballot
      BY <2>1, <2>2
   <2>4. \A bb \in Ballot, vv \in Value :
            SafeAt(bb, vv) => SafeAt(bb, vv)'
      BY <1>2, SafeAtStable
   <2> USE DEF TypeOK
   <2>10. CASE /\ b > maxBal[self]
               /\ maxBal' = [maxBal EXCEPT ![self] = b]
               /\ UNCHANGED votes
      <3>1. votes' = votes
         BY <2>10
      <3>2. \A a \in Acceptor : maxBal'[a] = (IF a = self THEN b ELSE maxBal[a])
         BY <2>10, <2>3
      <3>3. \A a \in Acceptor, bb \in Ballot, vv \in Value :
               VotedFor(a, bb, vv)' <=> VotedFor(a, bb, vv)
         BY <3>1 DEF VotedFor
      <3>4. \A a \in Acceptor, bb \in Ballot : DidNotVoteIn(a, bb)' <=> DidNotVoteIn(a, bb)
         BY <3>3 DEF DidNotVoteIn
      <3>5. TypeOK'
         <4>1. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]
            BY <3>1
         <4>2. maxBal' \in [Acceptor -> Ballot \cup {-1}]
            BY <2>10, <2>3 DEF Ballot
         <4>3. QED BY <4>1, <4>2
      <3>6. OneValuePerBallot'
         BY <3>3 DEF OneValuePerBallot
      <3>7. VotesSafe'
         BY <3>3, <2>4 DEF VotesSafe
      <3>8. NotVotedAbove'
         <4>1. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, maxBal'[a] < bb
               PROVE  DidNotVoteIn(a, bb)'
            <5>1. maxBal[a] < bb
               <6>1. maxBal[a] \leq maxBal'[a]
                  BY <3>2, <2>3, <2>10 DEF Ballot
               <6>2. QED BY <6>1, <4>1, <3>2, <2>3 DEF Ballot
            <5>2. DidNotVoteIn(a, bb)
               BY <5>1 DEF NotVotedAbove
            <5>3. QED BY <5>2, <3>4
         <4>2. QED BY <4>1 DEF NotVotedAbove
      <3>9. QED
         BY <3>5, <3>6, <3>7, <3>8 DEF Inv
   <2>20. CASE \E v \in Value :
                  /\ /\ maxBal[self] \leq b
                     /\ DidNotVoteIn(self, b)
                     /\ \A p \in Acceptor \ {self} :
                           \A w \in Value : VotedFor(p, b, w) => (w = v)
                     /\ SafeAt(b, v)
                  /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                  /\ maxBal' = [maxBal EXCEPT ![self] = b]
      <3>1. PICK v \in Value :
               /\ maxBal[self] \leq b
               /\ DidNotVoteIn(self, b)
               /\ \A p \in Acceptor \ {self} :
                     \A w \in Value : VotedFor(p, b, w) => (w = v)
               /\ SafeAt(b, v)
               /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
               /\ maxBal' = [maxBal EXCEPT ![self] = b]
         BY <2>20
      <3>2. \A a \in Acceptor : maxBal'[a] = (IF a = self THEN b ELSE maxBal[a])
         BY <3>1, <2>3
      <3>3. \A a \in Acceptor :
               votes'[a] = (IF a = self THEN votes[a] \cup {<<b, v>>} ELSE votes[a])
         BY <3>1, <2>3
      <3>4. \A a \in Acceptor, bb \in Ballot, vv \in Value :
               VotedFor(a, bb, vv)' <=>
                  (VotedFor(a, bb, vv) \/ (a = self /\ bb = b /\ vv = v))
         BY <3>3, <2>3 DEF VotedFor
      <3>5. TypeOK'
         <4>1. votes' \in [Acceptor -> SUBSET (Ballot \X Value)]
            <5>1. votes[self] \cup {<<b, v>>} \in SUBSET (Ballot \X Value)
               BY <2>3, <3>1
            <5>2. QED BY <3>1, <5>1, <2>3
         <4>2. maxBal' \in [Acceptor -> Ballot \cup {-1}]
            BY <3>1, <2>3 DEF Ballot
         <4>3. QED BY <4>1, <4>2
      <3>6. OneValuePerBallot'
         <4>1. ASSUME NEW a1 \in Acceptor, NEW a2 \in Acceptor, NEW bb \in Ballot,
                      NEW v1 \in Value, NEW v2 \in Value,
                      VotedFor(a1, bb, v1)', VotedFor(a2, bb, v2)'
               PROVE  v1 = v2
            <5>1. VotedFor(a1, bb, v1) \/ (a1 = self /\ bb = b /\ v1 = v)
               BY <4>1, <3>4
            <5>2. VotedFor(a2, bb, v2) \/ (a2 = self /\ bb = b /\ v2 = v)
               BY <4>1, <3>4
            <5>3. ASSUME NEW aa \in Acceptor, NEW vv \in Value, VotedFor(aa, b, vv)
                  PROVE  vv = v
               <6>1. aa # self
                  BY <5>3, <3>1 DEF DidNotVoteIn
               <6>2. QED BY <5>3, <6>1, <3>1
            <5>4. CASE VotedFor(a1, bb, v1) /\ VotedFor(a2, bb, v2)
               BY <5>4, <4>1 DEF OneValuePerBallot
            <5>5. CASE VotedFor(a1, bb, v1) /\ (a2 = self /\ bb = b /\ v2 = v)
               <6>1. v1 = v
                  BY <5>5, <5>3, <4>1
               <6>2. QED BY <6>1, <5>5
            <5>6. CASE (a1 = self /\ bb = b /\ v1 = v) /\ VotedFor(a2, bb, v2)
               <6>1. v2 = v
                  BY <5>6, <5>3, <4>1
               <6>2. QED BY <6>1, <5>6
            <5>7. CASE (a1 = self /\ bb = b /\ v1 = v) /\ (a2 = self /\ bb = b /\ v2 = v)
               BY <5>7
            <5>8. QED
               BY <5>1, <5>2, <5>4, <5>5, <5>6, <5>7
         <4>2. QED BY <4>1 DEF OneValuePerBallot
      <3>7. VotesSafe'
         <4>1. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, NEW vv \in Value,
                      VotedFor(a, bb, vv)'
               PROVE  SafeAt(bb, vv)'
            <5>1. VotedFor(a, bb, vv) \/ (a = self /\ bb = b /\ vv = v)
               BY <4>1, <3>4
            <5>2. SafeAt(bb, vv)
               <6>1. CASE VotedFor(a, bb, vv)
                  BY <6>1, <4>1 DEF VotesSafe
               <6>2. CASE a = self /\ bb = b /\ vv = v
                  BY <6>2, <3>1
               <6>3. QED BY <5>1, <6>1, <6>2
            <5>3. QED BY <5>2, <2>4, <4>1
         <4>2. QED BY <4>1 DEF VotesSafe
      <3>8. NotVotedAbove'
         <4>1. ASSUME NEW a \in Acceptor, NEW bb \in Ballot, maxBal'[a] < bb
               PROVE  DidNotVoteIn(a, bb)'
            <5>1. maxBal[a] < bb
               <6>1. maxBal[a] \leq maxBal'[a]
                  BY <3>2, <2>3, <3>1 DEF Ballot
               <6>2. QED BY <6>1, <4>1, <3>2, <2>3 DEF Ballot
            <5>2. DidNotVoteIn(a, bb)
               BY <5>1 DEF NotVotedAbove
            <5>3. bb # b \/ a # self
               <6>1. maxBal'[a] < bb
                  BY <4>1
               <6>2. CASE a = self
                  <7>1. maxBal'[self] = b
                     BY <3>2, <2>3
                  <7>2. b < bb
                     BY <6>1, <6>2, <7>1
                  <7>3. QED BY <7>2
               <6>3. QED BY <6>2
            <5>4. \A w \in Value : ~ VotedFor(a, bb, w)'
               <6>1. ASSUME NEW w \in Value PROVE ~ VotedFor(a, bb, w)'
                  <7>1. ~ (a = self /\ bb = b)
                     BY <5>3
                  <7>2. ~ VotedFor(a, bb, w)
                     BY <5>2 DEF DidNotVoteIn
                  <7>3. QED BY <7>1, <7>2, <3>4
               <6>2. QED BY <6>1
            <5>5. QED BY <5>4 DEF DidNotVoteIn
         <4>2. QED BY <4>1 DEF NotVotedAbove
      <3>9. QED
         BY <3>5, <3>6, <3>7, <3>8 DEF Inv
   <2>30. QED
      BY <2>2, <2>10, <2>20
<1>3. QED
   BY <1>1, <1>2 DEF vars

LEMMA GChosenSafe ==
  ASSUME NEW MB, NEW VT,
         \A a1, a2 \in Acceptor, bal \in Ballot, x1, x2 \in Value :
            (<<bal, x1>> \in VT[a1]) /\ (<<bal, x2>> \in VT[a2]) => (x1 = x2),
         \A a \in Acceptor, bal \in Ballot, x \in Value :
            (<<bal, x>> \in VT[a]) => GSafeAt(MB, VT, bal, x),
         NEW b1 \in Ballot, NEW b2 \in Ballot, NEW w1 \in Value, NEW w2 \in Value,
         GChosenIn(VT, b1, w1), GChosenIn(VT, b2, w2), b1 \leq b2
  PROVE  w1 = w2
<1>1. CASE b1 = b2
   <2>1. PICK Q1 \in Quorum : \A a \in Q1 : <<b1, w1>> \in VT[a]
      BY DEF GChosenIn
   <2>2. PICK Q2 \in Quorum : \A a \in Q2 : <<b2, w2>> \in VT[a]
      BY DEF GChosenIn
   <2>3. \E a \in Q1 : a \in Q2
      BY <2>1, <2>2, QA
   <2>4. PICK a \in Q1 : a \in Q2
      BY <2>3
   <2>5. a \in Acceptor
      BY <2>1, <2>4, QA
   <2>6. <<b1, w1>> \in VT[a] /\ <<b1, w2>> \in VT[a]
      BY <2>1, <2>2, <2>4, <1>1
   <2>7. QED
      BY <2>5, <2>6
<1>2. CASE b1 < b2
   <2>1. PICK Q \in Quorum : \A a \in Q : <<b2, w2>> \in VT[a]
      BY DEF GChosenIn
   <2>2. Q # {}
      BY <2>1, QuorumNonEmpty
   <2>3. PICK a \in Q : TRUE
      BY <2>2
   <2>4. a \in Acceptor
      BY <2>1, <2>3, QA
   <2>5. <<b2, w2>> \in VT[a]
      BY <2>1, <2>3
   <2>6. GSafeAt(MB, VT, b2, w2)
      BY <2>4, <2>5
   <2>7. \A c \in 0..(b2-1) : \A x \in Value : GChosenIn(VT, c, x) => (x = w2)
      BY <2>6, GSafeSound
   <2>8. b1 \in 0..(b2-1)
      BY <1>2 DEF Ballot
   <2>9. QED
      BY <2>7, <2>8
<1>3. QED
   BY <1>1, <1>2 DEF Ballot

LEMMA GConsistent ==
  ASSUME NEW MB, NEW VT,
         \A a1, a2 \in Acceptor, bal \in Ballot, x1, x2 \in Value :
            (<<bal, x1>> \in VT[a1]) /\ (<<bal, x2>> \in VT[a2]) => (x1 = x2),
         \A a \in Acceptor, bal \in Ballot, x \in Value :
            (<<bal, x>> \in VT[a]) => GSafeAt(MB, VT, bal, x),
         NEW w1 \in Value, NEW w2 \in Value,
         \E b1 \in Ballot : GChosenIn(VT, b1, w1),
         \E b2 \in Ballot : GChosenIn(VT, b2, w2)
  PROVE  w1 = w2
<1>1. PICK b1 \in Ballot : GChosenIn(VT, b1, w1)
   OBVIOUS
<1>2. PICK b2 \in Ballot : GChosenIn(VT, b2, w2)
   OBVIOUS
<1>3. CASE b1 \leq b2
   BY <1>1, <1>2, <1>3, GChosenSafe
<1>4. CASE b2 \leq b1
   <2>1. w2 = w1
      BY <1>1, <1>2, <1>4, GChosenSafe
   <2>2. QED BY <2>1
<1>5. QED
   BY <1>3, <1>4 DEF Ballot

LEMMA VotesMonotone ==
  ASSUME TypeOK, [Next]_vars,
         NEW a \in Acceptor, NEW bb \in Ballot, NEW vv \in Value, VotedFor(a, bb, vv)
  PROVE  VotedFor(a, bb, vv)'
<1>1. CASE vars' = vars
   BY <1>1 DEF vars, VotedFor
<1>2. CASE Next
   <2>1. PICK self \in Acceptor : acceptor(self)
      BY <1>2 DEF Next
   <2>2. PICK b \in Ballot :
            \/ /\ b > maxBal[self]
               /\ maxBal' = [maxBal EXCEPT ![self] = b]
               /\ UNCHANGED votes
            \/ /\ \E v \in Value :
                    /\ /\ maxBal[self] \leq b
                       /\ DidNotVoteIn(self, b)
                       /\ \A p \in Acceptor \ {self} :
                             \A w \in Value : VotedFor(p, b, w) => (w = v)
                       /\ SafeAt(b, v)
                    /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                    /\ maxBal' = [maxBal EXCEPT ![self] = b]
      BY <2>1 DEF acceptor
   <2>3. self \in Acceptor
      BY <2>1
   <2>4. CASE UNCHANGED votes
      BY <2>4 DEF VotedFor
   <2>5. CASE \E v \in Value :
                 votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
      <3>1. PICK v \in Value :
               votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
         BY <2>5
      <3>2. votes[a] \subseteq votes'[a]
         BY <3>1, <2>3 DEF TypeOK
      <3>3. QED
         BY <3>2 DEF VotedFor
   <2>6. QED
      BY <2>2, <2>4, <2>5
<1>3. QED
   BY <1>1, <1>2 DEF vars

THEOREM VT3 == Spec => C!Spec 
<1>1. Init => Inv
   BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'
   BY InvInv
<1>3. Init => C!Init
   <2> SUFFICES ASSUME Init PROVE C!Init
      OBVIOUS
   <2>1. \A bal \in Ballot, x \in Value : ~ ChosenIn(bal, x)
      <3>1. ASSUME NEW bal \in Ballot, NEW x \in Value, ChosenIn(bal, x)
            PROVE  FALSE
         <4>1. PICK Q \in Quorum : \A a \in Q : VotedFor(a, bal, x)
            BY <3>1 DEF ChosenIn
         <4>2. Q # {}
            BY <4>1, QuorumNonEmpty
         <4>3. PICK a \in Q : TRUE
            BY <4>2
         <4>4. a \in Acceptor
            BY <4>1, <4>3, QA
         <4>5. VotedFor(a, bal, x)
            BY <4>1, <4>3
         <4>6. QED
            BY <4>4, <4>5 DEF Init, VotedFor
      <3>2. QED BY <3>1
   <2>2. chosen = {}
      BY <2>1 DEF chosen
   <2>3. QED
      BY <2>2 DEF C!Init
<1>4. Inv /\ [Next]_vars => [C!Next]_(C!vars)
   <2> SUFFICES ASSUME Inv, [Next]_vars PROVE [C!Next]_(C!vars)
      OBVIOUS
   <2> USE DEF Inv
   <2>1. Inv'
      BY <1>2
   <2>2. \A bal \in Ballot, x \in Value : ChosenIn(bal, x) => ChosenIn(bal, x)'
      <3>1. ASSUME NEW bal \in Ballot, NEW x \in Value, ChosenIn(bal, x)
            PROVE  ChosenIn(bal, x)'
         <4>1. PICK Q \in Quorum : \A a \in Q : VotedFor(a, bal, x)
            BY <3>1 DEF ChosenIn
         <4>2. \A a \in Q : VotedFor(a, bal, x)'
            <5>1. ASSUME NEW a \in Q PROVE VotedFor(a, bal, x)'
               <6>1. a \in Acceptor
                  BY <4>1, <5>1, QA
               <6>2. VotedFor(a, bal, x)
                  BY <4>1, <5>1
               <6>3. QED
                  BY <6>1, <6>2, VotesMonotone
            <5>2. QED BY <5>1
         <4>3. QED BY <4>2 DEF ChosenIn
      <3>2. QED BY <3>1
   <2>3. chosen \subseteq chosen'
      BY <2>2 DEF chosen
   <2>4. \A u \in chosen, w \in chosen : u = w
      <3>1. ASSUME NEW u \in chosen, NEW w \in chosen PROVE u = w
         <4>1. u \in Value /\ (\E bal \in Ballot : ChosenIn(bal, u))
            BY <3>1 DEF chosen
         <4>2. w \in Value /\ (\E bal \in Ballot : ChosenIn(bal, w))
            BY <3>1 DEF chosen
         <4>3. \A a1, a2 \in Acceptor, bal \in Ballot, x1, x2 \in Value :
                  (<<bal, x1>> \in votes[a1]) /\ (<<bal, x2>> \in votes[a2]) => (x1 = x2)
            BY DEF OneValuePerBallot, VotedFor
         <4>4. \A a \in Acceptor, bal \in Ballot, x \in Value :
                  (<<bal, x>> \in votes[a]) => GSafeAt(maxBal, votes, bal, x)
            BY SafeAtIsG DEF VotesSafe, VotedFor
         <4>5. \E b1 \in Ballot : GChosenIn(votes, b1, u)
            BY <4>1 DEF ChosenIn, VotedFor, GChosenIn
         <4>6. \E b2 \in Ballot : GChosenIn(votes, b2, w)
            BY <4>2 DEF ChosenIn, VotedFor, GChosenIn
         <4>7. QED
            BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, GConsistent
      <3>2. QED BY <3>1
   <2>5. \A u \in chosen', w \in chosen' : u = w
      <3>1. ASSUME NEW u \in chosen', NEW w \in chosen' PROVE u = w
         <4>1. u \in Value /\ (\E bal \in Ballot : ChosenIn(bal, u)')
            BY <3>1 DEF chosen
         <4>2. w \in Value /\ (\E bal \in Ballot : ChosenIn(bal, w)')
            BY <3>1 DEF chosen
         <4>3. \A a1, a2 \in Acceptor, bal \in Ballot, x1, x2 \in Value :
                  (<<bal, x1>> \in votes'[a1]) /\ (<<bal, x2>> \in votes'[a2]) => (x1 = x2)
            BY <2>1 DEF Inv, OneValuePerBallot, VotedFor
         <4>4. \A a \in Acceptor, bal \in Ballot, x \in Value :
                  (<<bal, x>> \in votes'[a]) => GSafeAt(maxBal', votes', bal, x)
            BY <2>1, SafeAtIsGPrime DEF Inv, VotesSafe, VotedFor
         <4>5. \E b1 \in Ballot : GChosenIn(votes', b1, u)
            BY <4>1 DEF ChosenIn, VotedFor, GChosenIn
         <4>6. \E b2 \in Ballot : GChosenIn(votes', b2, w)
            BY <4>2 DEF ChosenIn, VotedFor, GChosenIn
         <4>7. QED
            BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, GConsistent
      <3>2. QED BY <3>1
   <2>6. chosen \subseteq Value /\ chosen' \subseteq Value
      BY DEF chosen
   <2>7. CASE chosen' = chosen
      BY <2>7 DEF C!vars
   <2>8. CASE chosen' # chosen
      <3>1. chosen = {}
         BY <2>3, <2>4, <2>5, <2>8
      <3>2. \E x \in Value : chosen' = {x}
         BY <3>1, <2>5, <2>6, <2>8
      <3>3. C!Next
         BY <3>1, <3>2 DEF C!Next
      <3>4. QED
         BY <3>3 DEF C!vars
   <2>9. QED
      BY <2>7, <2>8
<1>5. QED
   BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec, C!Spec
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

