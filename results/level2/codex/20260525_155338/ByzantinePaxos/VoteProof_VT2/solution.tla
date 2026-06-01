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

THEOREM NatInduction ==
  ASSUME NEW P(_),
         P(0),
         \A n \in Nat : P(n) => P(n+1)
  PROVE  \A n \in Nat : P(n)
BY IsaM("(intro natInduct, auto)")

THEOREM GeneralNatInduction ==
  ASSUME NEW P(_),
         \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
  PROVE  \A n \in Nat : P(n)
<1> DEFINE Q(n) == \A m \in 0..n : P(m)
<1>1. Q(0)  OBVIOUS
<1>2. \A n \in Nat : Q(n) => Q(n+1)  OBVIOUS
<1>3. \A n \in Nat : Q(n)  BY <1>1, <1>2, NatInduction, Isa
<1>4. QED BY <1>3

THEOREM RecursiveFcnOfNat ==
  ASSUME NEW Def(_,_),
         ASSUME NEW n \in Nat, NEW g, NEW h,
                \A i \in 0..(n-1) : g[i] = h[i]
         PROVE  Def(g, n) = Def(h, n)
  PROVE  LET f[n \in Nat] == Def(f, n)
         IN  f = [n \in Nat |-> Def(f, n)]
<1>. SUFFICES \E ff : ff = [n \in Nat |-> Def(ff, n)]
  OBVIOUS
<1>. DEFINE F[n \in Nat] == [i \in 0 .. n-1 |-> Def(F[n-1], i)]
            f[n \in Nat] == F[n+1][n]
<1>1. F = [n \in Nat |-> [i \in 0 .. n-1 |-> Def(F[n-1], i)]]
  <2>. SUFFICES \E FF : FF = [n \in Nat |-> [i \in 0 .. n-1 |-> Def(FF[n-1], i)]]
    BY Zenon
  <2>. DEFINE P(g,k) == g = [n \in 0 .. k |-> [i \in 0 .. n-1 |-> Def(g[n-1], i)]]
              G(k) == CHOOSE g : P(g,k)
              FF == [n \in Nat |-> [i \in 0 .. n-1 |-> G(n)[n][i] ]]
  <2>0. ASSUME NEW g, NEW k \in Nat, P(g,k),
               NEW n \in 0 .. k, NEW i \in 0 .. n-1
        PROVE  g[n][i] = Def(g[n-1], i)
    <3>. DEFINE gg == [m \in 0 .. k |-> [j \in 0 .. m-1 |-> Def(g[m-1], j)]]
    <3>1. gg[n][i] = Def(g[n-1],i)  OBVIOUS
    <3>2. g = gg  BY <2>0, Zenon
    <3>. QED  BY <3>1, <3>2, Zenon
  <2>1. \A k \in Nat : \E g : P(g,k)
    <3>. DEFINE Q(k) == \E g : P(g,k)
    <3>. SUFFICES \A k \in Nat : Q(k)  BY Zenon
    <3>1. Q(0)
      <4>. DEFINE g0 == [n \in {0} |-> [i \in {} |-> {}]]
      <4>1. P(g0, 0)  BY Isa
      <4>. QED  BY <4>1, Zenon
    <3>2. ASSUME NEW k \in Nat, Q(k)
          PROVE  Q(k+1)
      <4>1. PICK g : P(g,k)  BY <3>2, Zenon
      <4>1a. ASSUME NEW n \in 0 .. k, NEW i \in 0 .. n-1
             PROVE  g[n][i] = Def(g[n-1], i)
        BY <4>1, <2>0, Zenon
      <4>. DEFINE h == [n \in 0 .. k+1 |-> [i \in 0 .. n-1 |-> Def(g[n-1], i) ]]
      <4>2. h = [n \in 0 .. k+1 |-> [i \in 0 .. n-1 |-> Def(h[n-1], i)]]
        <5>. SUFFICES ASSUME NEW n \in 0 .. k+1, NEW i \in 0 .. n-1
                      PROVE  h[n][i] = Def(h[n-1], i)
          BY Zenon
        <5>1. h[n][i] = Def(g[n-1], i)  OBVIOUS
        <5>2. ASSUME NEW j \in 0 .. i-1
              PROVE  g[n-1][j] = h[n-1][j]
          BY <4>1a
        <5>. HIDE DEF h
        <5>3. Def(g[n-1],i) = Def(h[n-1],i)  BY <5>2
        <5>. QED  BY <5>1, <5>3
      <4>. HIDE DEF h
      <4>. QED  BY <4>2, Zenon
    <3>. HIDE DEF Q
    <3>. QED  BY <3>1, <3>2, NatInduction, IsaM("blast")
  <2>2. \A k \in Nat : P(G(k), k)  BY <2>1, Zenon
  <2>3. \A k \in Nat : \A l \in 0 .. k : \A i \in 0 .. l-1 : \A g,h :
           P(g,k) /\ P(h,l) => g[l][i] = h[l][i]
    <3>. DEFINE Q(k) == \A l \in 0 .. k : \A i \in 0 .. l-1 : \A g,h :
                           P(g,k) /\ P(h,l) => g[l][i] = h[l][i]
    <3>. SUFFICES \A k \in Nat : Q(k)  BY Zenon
    <3>0. Q(0)  OBVIOUS
    <3>1. ASSUME NEW k \in Nat, Q(k)
          PROVE  Q(k+1)
      <4>. HIDE DEF P
      <4>. SUFFICES ASSUME NEW l \in 1 .. k+1, NEW i \in 0 .. l-1, NEW g, NEW h,
                           P(g,k+1), P(h,l)
                    PROVE  g[l][i] = h[l][i]
        OBVIOUS
      <4>1. /\ g[l][i] = Def(g[l-1],i)
            /\ h[l][i] = Def(h[l-1],i)
        BY <2>0
      <4>. DEFINE gg == [nn \in 0 .. k |-> [ii \in 0 .. nn-1 |-> Def(g[nn-1],ii)]]
                  hh == [nn \in 0 .. l-1 |-> [ii \in 0 .. nn-1 |-> Def(h[nn-1],ii)]]
      <4>2. P(gg,k)
        <5>1. ASSUME NEW nn \in 0 .. k, NEW j \in 0 .. nn-1
              PROVE  gg[nn-1] = g[nn-1]
          <6>1. gg[nn-1] = [ii \in 0 .. nn-2 |-> Def(g[nn-2],ii)]
            OBVIOUS
          <6>2. g[nn-1] = [ii \in 0 .. (nn-1)-1 |-> Def(g[(nn-1)-1],ii)]
            BY nn-1 \in 0 .. k, nn-1 \in 0 .. k+1, Zenon DEF P
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY <5>1, Zenon DEF P
      <4>3. P(hh,l-1)
        <5>1. ASSUME NEW nn \in 0 .. l-1, NEW j \in 0 .. nn-1
              PROVE  hh[nn-1] = h[nn-1]
          <6>1. hh[nn-1] = [ii \in 0 .. nn-2 |-> Def(h[nn-2],ii)]
            OBVIOUS
          <6>2. h[nn-1] = [ii \in 0 .. (nn-1)-1 |-> Def(h[(nn-1)-1],ii)]
            BY nn-1 \in 0 .. l-1, nn-1 \in 0 .. l, Zenon DEF P
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY <5>1, Zenon DEF P
      <4>4. ASSUME NEW m \in 0 .. i-1
            PROVE  gg[l-1][m] = hh[l-1][m]
        <5>. HIDE DEF gg, hh
        <5>. QED  BY <3>1, <4>2, <4>3, l-1 \in 0 .. k, m \in 0 .. (l-1)-1
      <4>5. \A m \in 0 .. i-1 : g[l-1][m] = gg[l-1][m]   BY <2>0
      <4>6. \A m \in 0 .. i-1 : h[l-1][m] = hh[l-1][m]   BY <2>0
      <4>7. \A m \in 0 .. i-1 : g[l-1][m] = h[l-1][m]    BY <4>4, <4>5, <4>6, Zenon
      <4>8. Def(g[l-1],i) = Def(h[l-1],i)                BY <4>7
      <4>. QED  BY <4>8, <2>0
    <3>. HIDE DEF Q
    <3>. QED  BY <3>0, <3>1, NatInduction, IsaM("blast")
  <2>4. FF = [n \in Nat |-> [i \in 0 .. n-1 |-> Def(FF[n-1], i)]]
    <3>. HIDE DEF G
    <3>. SUFFICES ASSUME NEW k \in Nat, NEW i \in 0 .. k-1
                  PROVE  FF[k][i] = Def(FF[k-1], i)
      BY Zenon
    <3>1. FF[k][i] = G(k)[k][i]  OBVIOUS
    <3>2. G(k)[k][i] = Def(G(k)[k-1], i)  BY <2>2
    <3>. HIDE DEF P
    <3>3. \A j \in 0 .. i-1 : G(k)[k-1][j] = FF[k-1][j]  BY <2>2, <2>3 DEF G
    <3>. HIDE DEF FF
    <3>4. Def(G(k)[k-1], i) = Def(FF[k-1], i)  BY <3>3
    <3>. QED  BY <3>1, <3>2, <3>4
  <2>. QED  BY <2>4, Zenon
<1>. HIDE DEF F
<1>2. ASSUME NEW n \in Nat, NEW i \in 0 .. n-1
       PROVE  F[n][i] = Def(F[n-1], i)
  <2>. DEFINE G == [m \in Nat |-> [j \in 0 .. m-1 |-> Def(F[m-1],j)]]
  <2>1. G[n][i] = Def(F[n-1],i)  OBVIOUS
  <2>2. F = G  BY <1>1, Zenon
  <2>. QED  BY <2>1, <2>2, Zenon
<1>. DEFINE P(n) == \A m \in 0 .. n : \A i \in 0 .. m-1 : F[n][i] = F[m][i]
<1>3. \A n \in Nat : P(n)
  <2>1. ASSUME NEW n \in Nat, \A k \in 0 .. n-1 : P(k)
        PROVE  P(n)
    <3>. SUFFICES ASSUME NEW m \in 0 .. n, NEW i \in 0 .. m-1
                  PROVE  F[n][i] = F[m][i]
      OBVIOUS
    <3>2. CASE m = n  BY <3>2
    <3>3. CASE n = 0  BY <3>3, SMT
    <3>4. CASE 0 < n /\ m \in 0 .. n-1
      <4>1. F[n][i] = Def(F[n-1],i)  BY <1>2
      <4>2. \A j \in 0 .. i-1 : F[n-1][j] = F[m-1][j]  BY <2>1, <3>4
      <4>3. Def(F[n-1],i) = Def(F[m-1],i)  BY <4>2
      <4>4. Def(F[m-1],i) = F[m][i]  BY <1>2
      <4>. QED  BY <4>1, <4>3, <4>4
    <3>. QED  BY <3>2, <3>3, <3>4, SMT
  <2>. HIDE DEF P
  <2>. QED  BY <2>1, GeneralNatInduction, Blast
<1>4. f = [n \in Nat |-> Def(f,n)]
  <2>. SUFFICES ASSUME NEW n \in Nat
                PROVE  f[n] = Def(f,n)
    BY Zenon
  <2>1. f[n] = Def(F[n], n)  BY <1>2
  <2>2. \A i \in 0 .. n-1 : F[n][i] = f[i]  BY <1>3
  <2>3. Def(F[n],n) = Def(f,n)  BY <2>2, Zenon
  <2>. QED  BY <2>1, <2>3
<1>. QED  BY <1>4, Zenon

SafeAtStep(SA, bb, v) ==
  \/ bb = 0
  \/ \E Q \in Quorum :
       /\ \A a \in Q : maxBal[a] \geq bb
       /\ \E c \in -1..(bb-1) :
            /\ (c # -1) => /\ SA[c]
                           /\ \A a \in Q :
                                \A w \in Value :
                                   VotedFor(a, c, w) => (w = v)
            /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)

VotedForP(a, b, v) == <<b, v>> \in votes'[a]

DidNotVoteInP(a, b) == \A v \in Value : ~ VotedForP(a, b, v)

SafeAtStepP(SA, bb, v) ==
  \/ bb = 0
  \/ \E Q \in Quorum :
       /\ \A a \in Q : maxBal'[a] \geq bb
       /\ \E c \in -1..(bb-1) :
            /\ (c # -1) => /\ SA[c]
                           /\ \A a \in Q :
                                \A w \in Value :
                                   VotedForP(a, c, w) => (w = v)
            /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteInP(a, d)

LEMMA SafeAtProp ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v) = SafeAtStep([bb \in Ballot |-> SafeAt(bb, v)], b, v)
PROOF
  <1>1. ASSUME NEW v \in Value
        PROVE  LET SS[bb \in Nat] == SafeAtStep(SS, bb, v)
               IN  SS = [bb \in Nat |-> SafeAtStep(SS, bb, v)]
    <2>. DEFINE Def(ff, nn) == SafeAtStep(ff, nn, v)
                SS[bb \in Nat] == Def(SS, bb)
    <2>1. ASSUME NEW n \in Nat,
                  NEW g,
                  NEW h,
                  \A i \in 0..(n-1) : g[i] = h[i]
          PROVE  Def(g, n) = Def(h, n)
      BY <2>1 DEF Def, SafeAtStep, VotedFor, DidNotVoteIn, Ballot
    <2>. HIDE DEF Def
    <2>2. SS = [bb \in Nat |-> Def(SS, bb)]
      BY <2>1, RecursiveFcnOfNat, Isa
    <2>. QED BY <2>2 DEF SS, Def
  <1>2. ASSUME NEW b \in Ballot, NEW v \in Value
        PROVE  SafeAt(b, v) =
                 SafeAtStep([bb \in Ballot |-> SafeAt(bb, v)], b, v)
    <2>. DEFINE SS[bb \in Nat] == SafeAtStep(SS, bb, v)
    <2>1. SS = [bb \in Nat |-> SafeAtStep(SS, bb, v)]
      BY <1>1 DEF SS
    <2>2. \A bb \in Ballot : SafeAt(bb, v) = SS[bb]
      BY DEF SafeAt, SafeAtStep, SS, Ballot
    <2>3. [bb \in Ballot |-> SafeAt(bb, v)] = SS
      BY <2>1, <2>2 DEF Ballot
    <2>4. SS[b] = SafeAtStep(SS, b, v)
      BY <2>1 DEF Ballot
    <2>. QED BY <2>2, <2>3, <2>4
  <1>. QED BY <1>2

LEMMA SafeAtPropPrime ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v)' = SafeAtStepP([bb \in Ballot |-> SafeAt(bb, v)'], b, v)
PROOF
  <1>1. ASSUME NEW v \in Value
        PROVE  LET SS[bb \in Nat] == SafeAtStepP(SS, bb, v)
               IN  SS = [bb \in Nat |-> SafeAtStepP(SS, bb, v)]
    <2>. DEFINE Def(ff, nn) == SafeAtStepP(ff, nn, v)
                SS[bb \in Nat] == Def(SS, bb)
    <2>1. ASSUME NEW n \in Nat,
                  NEW g,
                  NEW h,
                  \A i \in 0..(n-1) : g[i] = h[i]
          PROVE  Def(g, n) = Def(h, n)
      BY <2>1 DEF Def, SafeAtStepP, VotedForP, DidNotVoteInP, Ballot
    <2>. HIDE DEF Def
    <2>2. SS = [bb \in Nat |-> Def(SS, bb)]
      BY <2>1, RecursiveFcnOfNat, Isa
    <2>. QED BY <2>2 DEF SS, Def
  <1>2. ASSUME NEW b \in Ballot, NEW v \in Value
        PROVE  SafeAt(b, v)' =
                 SafeAtStepP([bb \in Ballot |-> SafeAt(bb, v)'], b, v)
    <2>. DEFINE SS[bb \in Nat] == SafeAtStepP(SS, bb, v)
    <2>1. SS = [bb \in Nat |-> SafeAtStepP(SS, bb, v)]
      BY <1>1 DEF SS
    <2>2. \A bb \in Ballot : SafeAt(bb, v)' = SS[bb]
      BY DEF SafeAt, SafeAtStepP, VotedForP, DidNotVoteInP,
             VotedFor, DidNotVoteIn, SS, Ballot
    <2>3. [bb \in Ballot |-> SafeAt(bb, v)'] = SS
      BY <2>1, <2>2 DEF Ballot
    <2>4. SS[b] = SafeAtStepP(SS, b, v)
      BY <2>1 DEF Ballot
    <2>. QED BY <2>2, <2>3, <2>4
  <1>. QED BY <1>2

VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value :
           VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

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

LEMMA VInv3ImpliesVInv1 == VInv3 => VInv1
PROOF
  BY DEF VInv1, VInv3

LEMMA NextDef ==
  Next =  \E self \in Acceptor : \E b \in Ballot : BallotAction(self, b)
PROOF
  BY DEF Next, acceptor, BallotAction, IncreaseMaxBal, VoteFor

LEMMA InitImpliesInv == Init => VInv
PROOF
  BY DEF Init, VInv, TypeOK, VInv2, VInv3, VInv4, VotedFor, DidNotVoteIn, Ballot

LEMMA StutterInv == VInv /\ UNCHANGED vars => VInv'
PROOF
  BY DEF VInv, TypeOK, VInv2, VInv3, VInv4, VotedFor, DidNotVoteIn, SafeAt, vars

LEMMA IntervalNat ==
  \A n \in Nat :
    \A c \in -1..(n-1) :
      c # -1 => c \in Ballot /\ c \in 0..(n-1)
PROOF
  BY DEF Ballot

LEMMA NonnegIntervalNat ==
  \A n \in Nat :
    \A c \in 0..(n-1) :
      c \in Ballot
PROOF
  BY DEF Ballot

LEMMA ExceptAt ==
  \A S, T :
    \A f \in [S -> T] :
      \A x \in S :
        \A e : [f EXCEPT ![x] = e][x] = e
PROOF
  OBVIOUS

LEMMA ExceptOther ==
  \A S, T :
    \A f \in [S -> T] :
      \A x \in S :
        \A y \in S :
          \A e : y # x => [f EXCEPT ![x] = e][y] = f[y]
PROOF
  OBVIOUS

LEMMA IncreaseMaxBalPreservesMax ==
  \A self \in Acceptor, mb \in Ballot :
    TypeOK /\ IncreaseMaxBal(self, mb) =>
      \A a \in Acceptor, x \in Int :
        maxBal[a] >= x => maxBal'[a] >= x
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW mb \in Ballot,
                TypeOK,
                IncreaseMaxBal(self, mb),
                NEW a \in Acceptor,
                NEW x \in Int,
                maxBal[a] >= x
        PROVE  maxBal'[a] >= x
    <2>1. CASE a = self
      <3>1. maxBal'[a] = mb
        BY <1>1, <2>1, ExceptAt DEF IncreaseMaxBal, TypeOK
      <3>2. mb > maxBal[a]
        BY <1>1, <2>1 DEF IncreaseMaxBal
      <3>3. maxBal[a] >= x
        BY <1>1
      <3>4. maxBal[a] \in Int
        BY <1>1 DEF TypeOK, Ballot
      <3>5. mb \in Int
        BY <1>1 DEF Ballot
      <3>6. mb >= x
        BY <3>2, <3>3, <3>4, <3>5, SMT
      <3>. QED BY <3>1, <3>6
    <2>2. CASE a # self
      <3>1. maxBal'[a] = maxBal[a]
        BY <1>1, <2>2, ExceptOther DEF IncreaseMaxBal, TypeOK
      <3>. QED BY <1>1, <3>1
    <2>. QED BY <2>1, <2>2
  <1>. QED BY <1>1

LEMMA IncreaseMaxBalPreservesVotes ==
  \A self \in Acceptor, mb \in Ballot :
    IncreaseMaxBal(self, mb) =>
      /\ \A a, b, v : (VotedForP(a, b, v) <=> VotedFor(a, b, v))
      /\ \A a, b : (DidNotVoteInP(a, b) <=> DidNotVoteIn(a, b))
PROOF
  BY DEF IncreaseMaxBal, VotedFor, VotedForP, DidNotVoteIn, DidNotVoteInP

LEMMA IncreaseMaxBalReflectsLower ==
  \A self \in Acceptor, mb \in Ballot :
    TypeOK /\ IncreaseMaxBal(self, mb) =>
      \A a \in Acceptor, bb \in Ballot :
        maxBal'[a] < bb => maxBal[a] < bb
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW mb \in Ballot,
                TypeOK,
                IncreaseMaxBal(self, mb),
                NEW a \in Acceptor,
                NEW bb \in Ballot,
                maxBal'[a] < bb
        PROVE  maxBal[a] < bb
    <2>1. CASE a = self
      <3>1. maxBal'[a] = mb
        BY <1>1, <2>1, ExceptAt DEF IncreaseMaxBal, TypeOK
      <3>2. mb > maxBal[a]
        BY <1>1, <2>1 DEF IncreaseMaxBal
      <3>3. mb < bb
        BY <1>1, <3>1
      <3>4. maxBal[a] \in Int
        BY <1>1 DEF TypeOK, Ballot
      <3>5. mb \in Int
        BY <1>1 DEF Ballot
      <3>6. bb \in Int
        BY <1>1 DEF Ballot
      <3>. QED BY <3>2, <3>3, <3>4, <3>5, <3>6, SMT
    <2>2. CASE a # self
      <3>1. maxBal'[a] = maxBal[a]
        BY <1>1, <2>2, ExceptOther DEF IncreaseMaxBal, TypeOK
      <3>. QED BY <1>1, <3>1
    <2>. QED BY <2>1, <2>2
  <1>. QED BY <1>1

LEMMA VoteForVotedForPrime ==
  \A self \in Acceptor, b \in Ballot, v \in Value :
    TypeOK /\ VoteFor(self, b, v) =>
      \A a \in Acceptor, bb \in Ballot, w \in Value :
        (VotedFor(a, bb, w)' <=>
          \/ VotedFor(a, bb, w)
          \/ /\ a = self
             /\ bb = b
             /\ w = v)
PROOF
  BY ExceptAt, ExceptOther DEF TypeOK, VoteFor, VotedFor, Ballot

LEMMA VoteForDidNotVoteInPrime ==
  \A self \in Acceptor, b \in Ballot, v \in Value :
    TypeOK /\ VoteFor(self, b, v) =>
      \A a \in Acceptor, bb \in Ballot :
        bb # b /\ DidNotVoteIn(a, bb) => DidNotVoteIn(a, bb)'
PROOF
  BY VoteForVotedForPrime DEF DidNotVoteIn

LEMMA VoteForReflectsLower ==
  \A self \in Acceptor, b \in Ballot, v \in Value :
    TypeOK /\ VoteFor(self, b, v) =>
      \A a \in Acceptor, bb \in Ballot :
        maxBal'[a] < bb => maxBal[a] < bb
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW b \in Ballot,
                NEW v \in Value,
                TypeOK,
                VoteFor(self, b, v),
                NEW a \in Acceptor,
                NEW bb \in Ballot,
                maxBal'[a] < bb
        PROVE maxBal[a] < bb
    <2>1. CASE a = self
      <3>1. maxBal'[a] = b
        BY <1>1, <2>1, ExceptAt DEF VoteFor, TypeOK
      <3>2. maxBal[a] <= b
        BY <1>1, <2>1 DEF VoteFor
      <3>3. b < bb
        BY <1>1, <3>1
      <3>4. maxBal[a] \in Int
        BY <1>1 DEF TypeOK, Ballot
      <3>5. b \in Int /\ bb \in Int
        BY <1>1 DEF Ballot
      <3>. QED BY <3>2, <3>3, <3>4, <3>5, SMT
    <2>2. CASE a # self
      <3>1. maxBal'[a] = maxBal[a]
        BY <1>1, <2>2, ExceptOther DEF VoteFor, TypeOK
      <3>. QED BY <1>1, <3>1
    <2>. QED BY <2>1, <2>2
  <1>. QED BY <1>1

LEMMA VoteForPreservesMax ==
  \A self \in Acceptor, b \in Ballot, v \in Value :
    TypeOK /\ VoteFor(self, b, v) =>
      \A a \in Acceptor, x \in Int :
        maxBal[a] >= x => maxBal'[a] >= x
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW b \in Ballot,
                NEW v \in Value,
                TypeOK,
                VoteFor(self, b, v),
                NEW a \in Acceptor,
                NEW x \in Int,
                maxBal[a] >= x
        PROVE maxBal'[a] >= x
    <2>1. CASE a = self
      <3>1. maxBal'[a] = b
        BY <1>1, <2>1, ExceptAt DEF VoteFor, TypeOK
      <3>2. maxBal[a] <= b
        BY <1>1, <2>1 DEF VoteFor
      <3>3. maxBal[a] >= x
        BY <1>1
      <3>4. maxBal[a] \in Int
        BY <1>1 DEF TypeOK, Ballot
      <3>5. b \in Int
        BY <1>1 DEF Ballot
      <3>6. b >= x
        BY <3>2, <3>3, <3>4, <3>5, SMT
      <3>. QED BY <3>1, <3>6
    <2>2. CASE a # self
      <3>1. maxBal'[a] = maxBal[a]
        BY <1>1, <2>2, ExceptOther DEF VoteFor, TypeOK
      <3>. QED BY <1>1, <3>1
    <2>. QED BY <2>1, <2>2
  <1>. QED BY <1>1

LEMMA VoteForPreservesDidNotVoteInStep ==
  \A self \in Acceptor, b \in Ballot, v \in Value :
    VInv /\ VoteFor(self, b, v) =>
      \A a \in Acceptor :
        \A n \in Ballot :
          \A d \in 0..(n-1) :
            maxBal[a] >= n /\ DidNotVoteIn(a, d) => DidNotVoteInP(a, d)
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW b \in Ballot,
                NEW v \in Value,
                VInv,
                VoteFor(self, b, v),
                NEW a \in Acceptor,
                NEW n \in Ballot,
                NEW d \in 0..(n-1),
                maxBal[a] >= n,
                DidNotVoteIn(a, d)
        PROVE DidNotVoteInP(a, d)
    <2>1. ASSUME NEW u \in Value, VotedForP(a, d, u)
          PROVE FALSE
      <3>0. d \in Ballot
        BY <1>1, NonnegIntervalNat DEF Ballot
      <3>1. \/ VotedFor(a, d, u)
             \/ /\ a = self /\ d = b /\ u = v
        BY <1>1, <2>1, <3>0, VoteForVotedForPrime DEF VInv, VotedFor, VotedForP
      <3>2. CASE VotedFor(a, d, u)
        BY <1>1, <2>1, <3>2 DEF DidNotVoteIn
      <3>3. CASE /\ a = self /\ d = b /\ u = v
        <4>1. maxBal[self] <= b
          BY <1>1 DEF VoteFor
        <4>2. maxBal[self] >= n
          BY <1>1, <3>3
        <4>3. b \in 0..(n-1)
          BY <1>1, <3>3
        <4>4. b \in Int /\ n \in Int
          BY <1>1 DEF Ballot
        <4>5. maxBal[self] \in Int
          BY <1>1, <3>3 DEF VInv, TypeOK, Ballot
        <4>. QED BY <4>1, <4>2, <4>3, <4>4, <4>5, SMT
      <3>. QED BY <3>1, <3>2, <3>3
    <2>. QED BY <2>1 DEF DidNotVoteInP
  <1>. QED BY <1>1

LEMMA VoteForPreservesVoteValueStep ==
  \A self \in Acceptor, b \in Ballot, v \in Value :
    VInv /\ VoteFor(self, b, v) =>
      \A a \in Acceptor :
        \A n \in Ballot :
          \A c \in 0..(n-1) :
            \A w \in Value :
              maxBal[a] >= n /\
              (\A u \in Value : VotedFor(a, c, u) => u = w)
              =>
              (\A u \in Value : VotedForP(a, c, u) => u = w)
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW b \in Ballot,
                NEW v \in Value,
                VInv,
                VoteFor(self, b, v),
                NEW a \in Acceptor,
                NEW n \in Ballot,
                NEW c \in 0..(n-1),
                NEW w \in Value,
                maxBal[a] >= n,
                \A u \in Value : VotedFor(a, c, u) => u = w
        PROVE \A u \in Value : VotedForP(a, c, u) => u = w
    <2>1. ASSUME NEW u \in Value, VotedForP(a, c, u)
          PROVE u = w
      <3>0. c \in Ballot
        BY <1>1, NonnegIntervalNat DEF Ballot
      <3>1. \/ VotedFor(a, c, u)
             \/ /\ a = self /\ c = b /\ u = v
        BY <1>1, <2>1, <3>0, VoteForVotedForPrime DEF VInv, VotedFor, VotedForP
      <3>2. CASE VotedFor(a, c, u)
        BY <1>1, <3>2
      <3>3. CASE /\ a = self /\ c = b /\ u = v
        <4>1. maxBal[self] <= b
          BY <1>1 DEF VoteFor
        <4>2. maxBal[self] >= n
          BY <1>1, <3>3
        <4>3. b \in 0..(n-1)
          BY <1>1, <3>3
        <4>4. FALSE
          <5>1. b \in Int /\ n \in Int
            BY <1>1 DEF Ballot
          <5>2. maxBal[self] \in Int
            BY <1>1, <3>3 DEF VInv, TypeOK, Ballot
          <5>. QED BY <4>1, <4>2, <4>3, <5>1, <5>2, SMT
        <4>. QED BY <4>4
      <3>. QED BY <3>1, <3>2, <3>3
    <2>. QED BY <2>1
  <1>. QED BY <1>1

LEMMA IncreaseMaxBalSafeAt ==
  \A self \in Acceptor, mb \in Ballot :
    TypeOK /\ IncreaseMaxBal(self, mb) =>
      \A bb \in Ballot, v \in Value : SafeAt(bb, v) => SafeAt(bb, v)'
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW mb \in Ballot,
                TypeOK,
                IncreaseMaxBal(self, mb)
        PROVE  \A bb \in Ballot, v \in Value : SafeAt(bb, v) => SafeAt(bb, v)'
    <2>. DEFINE P(n) == \A v \in Value : SafeAt(n, v) => SafeAt(n, v)'
    <2>1. ASSUME NEW n \in Nat,
                  \A m \in 0..(n-1) : P(m)
          PROVE  P(n)
      <3>. SUFFICES ASSUME NEW v \in Value, SafeAt(n, v)
                    PROVE  SafeAt(n, v)'
        OBVIOUS
      <3>1. SafeAtStep([bb \in Ballot |-> SafeAt(bb, v)], n, v)
        BY SafeAtProp DEF Ballot
      <3>2. SafeAtStepP([bb \in Ballot |-> SafeAt(bb, v)'], n, v)
        <4>1. CASE n = 0
          BY <4>1 DEF SafeAtStepP
        <4>2. CASE n # 0
          <5>1. \E Q \in Quorum :
                   /\ \A a \in Q : maxBal[a] >= n
                   /\ \E c \in -1..(n-1) :
                        /\ (c # -1) =>
                             /\ [bb \in Ballot |-> SafeAt(bb, v)][c]
                             /\ \A a \in Q :
                                  \A w \in Value :
                                    VotedFor(a, c, w) => (w = v)
                        /\ \A d \in (c+1)..(n-1), a \in Q : DidNotVoteIn(a, d)
            BY <3>1, <4>2 DEF SafeAtStep
          <5>2. PICK Q \in Quorum :
                   /\ \A a \in Q : maxBal[a] >= n
                   /\ \E c \in -1..(n-1) :
                        /\ (c # -1) =>
                             /\ [bb \in Ballot |-> SafeAt(bb, v)][c]
                             /\ \A a \in Q :
                                  \A w \in Value :
                                    VotedFor(a, c, w) => (w = v)
                        /\ \A d \in (c+1)..(n-1), a \in Q : DidNotVoteIn(a, d)
            BY <5>1
          <5>3. PICK c \in -1..(n-1) :
                        /\ (c # -1) =>
                             /\ [bb \in Ballot |-> SafeAt(bb, v)][c]
                             /\ \A a \in Q :
                                  \A w \in Value :
                                    VotedFor(a, c, w) => (w = v)
                        /\ \A d \in (c+1)..(n-1), a \in Q : DidNotVoteIn(a, d)
            BY <5>2
          <5>4. \A a \in Q : maxBal'[a] >= n
            BY <1>1, <5>2, QA, IncreaseMaxBalPreservesMax
          <5>5. (c # -1) =>
                   /\ [bb \in Ballot |-> SafeAt(bb, v)'][c]
                   /\ \A a \in Q :
                        \A w \in Value :
                          VotedForP(a, c, w) => (w = v)
            <6>1. ASSUME c # -1
                  PROVE  /\ [bb \in Ballot |-> SafeAt(bb, v)'][c]
                         /\ \A a \in Q :
                              \A w \in Value :
                                VotedForP(a, c, w) => (w = v)
              <7>1. c \in Ballot /\ c \in 0..(n-1)
                BY <5>3, <6>1, IntervalNat
              <7>2. SafeAt(c, v)
                BY <5>3, <6>1, <7>1
              <7>3. P(c)
                BY <2>1, <7>1 DEF P
              <7>4. SafeAt(c, v)'
                BY <7>2, <7>3 DEF P
              <7>5. [bb \in Ballot |-> SafeAt(bb, v)'][c]
                BY <7>1, <7>4
              <7>6. \A a \in Q :
                       \A w \in Value :
                         VotedForP(a, c, w) => (w = v)
                BY <1>1, <5>3, <6>1, IncreaseMaxBalPreservesVotes
              <7>. QED BY <7>5, <7>6
            <6>. QED BY <6>1
          <5>6. \A d \in (c+1)..(n-1), a \in Q : DidNotVoteInP(a, d)
            BY <1>1, <5>3, IncreaseMaxBalPreservesVotes
          <5>. QED BY <5>2, <5>3, <5>4, <5>5, <5>6 DEF SafeAtStepP
        <4>. QED BY <4>1, <4>2
      <3>. QED BY <3>2, SafeAtPropPrime DEF Ballot
    <2>2. \A n \in Nat : P(n)
      BY <2>1, GeneralNatInduction, Isa
    <2>. QED BY <2>2 DEF P, Ballot
  <1>. QED BY <1>1

LEMMA VoteForSafeAtPreserved ==
  \A self \in Acceptor, b \in Ballot, v \in Value :
    VInv /\ VoteFor(self, b, v) =>
      \A bb \in Ballot, w \in Value : SafeAt(bb, w) => SafeAt(bb, w)'
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW b \in Ballot,
                NEW v \in Value,
                VInv,
                VoteFor(self, b, v)
        PROVE  \A bb \in Ballot, w \in Value : SafeAt(bb, w) => SafeAt(bb, w)'
    <2>. DEFINE P(n) == \A w \in Value : SafeAt(n, w) => SafeAt(n, w)'
    <2>1. ASSUME NEW n \in Nat,
                  \A m \in 0..(n-1) : P(m)
          PROVE  P(n)
      <3>. SUFFICES ASSUME NEW w \in Value, SafeAt(n, w)
                    PROVE  SafeAt(n, w)'
        OBVIOUS
      <3>1. SafeAtStep([bb \in Ballot |-> SafeAt(bb, w)], n, w)
        BY SafeAtProp DEF Ballot
      <3>2. SafeAtStepP([bb \in Ballot |-> SafeAt(bb, w)'], n, w)
        <4>1. CASE n = 0
          BY <4>1 DEF SafeAtStepP
        <4>2. CASE n # 0
          <5>1. \E Q \in Quorum :
                   /\ \A a \in Q : maxBal[a] >= n
                   /\ \E c \in -1..(n-1) :
                        /\ (c # -1) =>
                             /\ [bb \in Ballot |-> SafeAt(bb, w)][c]
                             /\ \A a \in Q :
                                  \A u \in Value :
                                    VotedFor(a, c, u) => (u = w)
                        /\ \A d \in (c+1)..(n-1), a \in Q : DidNotVoteIn(a, d)
            BY <3>1, <4>2 DEF SafeAtStep
          <5>2. PICK Q \in Quorum :
                   /\ \A a \in Q : maxBal[a] >= n
                   /\ \E c \in -1..(n-1) :
                        /\ (c # -1) =>
                             /\ [bb \in Ballot |-> SafeAt(bb, w)][c]
                             /\ \A a \in Q :
                                  \A u \in Value :
                                    VotedFor(a, c, u) => (u = w)
                        /\ \A d \in (c+1)..(n-1), a \in Q : DidNotVoteIn(a, d)
            BY <5>1
          <5>3. PICK c \in -1..(n-1) :
                        /\ (c # -1) =>
                             /\ [bb \in Ballot |-> SafeAt(bb, w)][c]
                             /\ \A a \in Q :
                                  \A u \in Value :
                                    VotedFor(a, c, u) => (u = w)
                        /\ \A d \in (c+1)..(n-1), a \in Q : DidNotVoteIn(a, d)
            BY <5>2
          <5>4. \A a \in Q : maxBal'[a] >= n
            BY <1>1, <5>2, QA, VoteForPreservesMax DEF VInv
          <5>5. (c # -1) =>
                   /\ [bb \in Ballot |-> SafeAt(bb, w)'][c]
                   /\ \A a \in Q :
                        \A u \in Value :
                          VotedForP(a, c, u) => (u = w)
            <6>1. ASSUME c # -1
                  PROVE  /\ [bb \in Ballot |-> SafeAt(bb, w)'][c]
                         /\ \A a \in Q :
                              \A u \in Value :
                                VotedForP(a, c, u) => (u = w)
              <7>1. c \in Ballot /\ c \in 0..(n-1)
                BY <5>3, <6>1, IntervalNat
              <7>2. SafeAt(c, w)
                BY <5>3, <6>1, <7>1
              <7>3. P(c)
                BY <2>1, <7>1 DEF P
              <7>4. SafeAt(c, w)'
                BY <7>2, <7>3 DEF P
              <7>5. [bb \in Ballot |-> SafeAt(bb, w)'][c]
                BY <7>1, <7>4
              <7>6. \A a \in Q :
                       \A u \in Value :
                         VotedForP(a, c, u) => (u = w)
                <8>1. ASSUME NEW a \in Q,
                              NEW u \in Value,
                              VotedForP(a, c, u)
                      PROVE u = w
                  <9>1. a \in Acceptor
                    BY <8>1, QA
                  <9>2. maxBal[a] >= n
                    BY <5>2, <8>1
                  <9>3. \A uu \in Value : VotedFor(a, c, uu) => uu = w
                    BY <5>3, <6>1, <8>1
                  <9>4. n \in Ballot
                    BY DEF Ballot
                  <9>5. c \in 0..(n-1)
                    BY <7>1
                  <9>6. \A uu \in Value : VotedForP(a, c, uu) => uu = w
                    BY <1>1, <9>1, <9>2, <9>3, <9>4, <9>5,
                       VoteForPreservesVoteValueStep
                       DEF VInv
                  <9>. QED BY <8>1, <9>6
                <8>. QED BY <8>1
              <7>. QED BY <7>5, <7>6
            <6>. QED BY <6>1
          <5>6. \A d \in (c+1)..(n-1), a \in Q : DidNotVoteInP(a, d)
            BY <1>1, <5>2, <5>3, QA, VoteForPreservesDidNotVoteInStep
               DEF VInv, Ballot
          <5>. QED BY <5>2, <5>3, <5>4, <5>5, <5>6 DEF SafeAtStepP
        <4>. QED BY <4>1, <4>2
      <3>. QED BY <3>2, SafeAtPropPrime DEF Ballot
    <2>2. \A n \in Nat : P(n)
      BY <2>1, GeneralNatInduction, Isa
    <2>. QED BY <2>2 DEF P, Ballot
  <1>. QED BY <1>1

LEMMA IncreaseMaxBalInv ==
  \A self \in Acceptor, b \in Ballot :
    VInv /\ IncreaseMaxBal(self, b) => VInv'
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW b \in Ballot,
                VInv,
                IncreaseMaxBal(self, b)
        PROVE  VInv'
    <2>1. TypeOK'
      BY <1>1, ExceptAt, ExceptOther
         DEF VInv, TypeOK, IncreaseMaxBal, Ballot
    <2>2. VInv2'
      <3>1. ASSUME NEW a \in Acceptor,
                    NEW bb \in Ballot,
                    NEW v \in Value,
                    VotedFor(a, bb, v)'
              PROVE SafeAt(bb, v)'
        <4>1. VotedFor(a, bb, v)
          BY <1>1, <3>1 DEF IncreaseMaxBal, VotedFor
        <4>2. SafeAt(bb, v)
          BY <1>1, <4>1 DEF VInv, VInv2
        <4>. QED BY <1>1, <4>2, IncreaseMaxBalSafeAt DEF VInv
      <3>. QED BY <3>1 DEF VInv2
    <2>3. VInv3'
      BY <1>1 DEF VInv, VInv3, IncreaseMaxBal, VotedFor
    <2>4. VInv4'
      <3>1. ASSUME NEW a \in Acceptor,
                    NEW bb \in Ballot,
                    maxBal'[a] < bb
              PROVE DidNotVoteIn(a, bb)'
        <4>1. maxBal[a] < bb
          BY <1>1, <3>1, IncreaseMaxBalReflectsLower DEF VInv
        <4>2. DidNotVoteIn(a, bb)
          BY <1>1, <4>1 DEF VInv, VInv4
        <4>. QED BY <1>1, <4>2 DEF IncreaseMaxBal, DidNotVoteIn, VotedFor
      <3>. QED BY <3>1 DEF VInv4
    <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF VInv
  <1>. QED BY <1>1

LEMMA VoteForInv ==
  \A self \in Acceptor, b \in Ballot, v \in Value :
    VInv /\ VoteFor(self, b, v) => VInv'
PROOF
  <1>1. ASSUME NEW self \in Acceptor,
                NEW b \in Ballot,
                NEW v \in Value,
                VInv,
                VoteFor(self, b, v)
        PROVE VInv'
    <2>1. TypeOK'
      BY <1>1, ExceptAt, ExceptOther
         DEF VInv, TypeOK, VoteFor, VotedFor, Ballot
    <2>2. VInv3'
      BY <1>1, VoteForVotedForPrime
         DEF VInv, VInv3, VoteFor, VotedFor, DidNotVoteIn
    <2>3. VInv4'
      <3>1. ASSUME NEW a \in Acceptor,
                    NEW bb \in Ballot,
                    maxBal'[a] < bb
              PROVE DidNotVoteIn(a, bb)'
        <4>1. ASSUME NEW w \in Value,
                      VotedFor(a, bb, w)'
                PROVE FALSE
          <5>1. \/ VotedFor(a, bb, w)
                 \/ /\ a = self /\ bb = b /\ w = v
            BY <1>1, <4>1, VoteForVotedForPrime DEF VInv
          <5>2. CASE VotedFor(a, bb, w)
            <6>1. maxBal[a] < bb
              BY <1>1, <3>1, VoteForReflectsLower DEF VInv
            <6>2. DidNotVoteIn(a, bb)
              BY <1>1, <6>1 DEF VInv, VInv4
            <6>. QED BY <5>2, <6>2 DEF DidNotVoteIn
          <5>3. CASE /\ a = self /\ bb = b /\ w = v
            <6>1. maxBal'[a] = bb
              BY <1>1, <5>3, ExceptAt DEF VoteFor, VInv, TypeOK
            <6>. QED BY <3>1, <6>1
          <5>. QED BY <5>1, <5>2, <5>3
        <4>. QED BY <4>1 DEF DidNotVoteIn
      <3>. QED BY <3>1 DEF VInv4
    <2>4. VInv2'
      <3>1. ASSUME NEW a \in Acceptor,
                    NEW bb \in Ballot,
                    NEW w \in Value,
                    VotedFor(a, bb, w)'
              PROVE SafeAt(bb, w)'
        <4>1. \/ VotedFor(a, bb, w)
               \/ /\ a = self /\ bb = b /\ w = v
          BY <1>1, <3>1, VoteForVotedForPrime DEF VInv
        <4>2. CASE VotedFor(a, bb, w)
          <5>1. SafeAt(bb, w)
            BY <1>1, <4>2 DEF VInv, VInv2
          <5>. QED BY <1>1, <5>1, VoteForSafeAtPreserved
        <4>3. CASE /\ a = self /\ bb = b /\ w = v
          <5>1. SafeAt(bb, w)
            BY <1>1, <4>3 DEF VoteFor
          <5>. QED BY <1>1, <5>1, VoteForSafeAtPreserved
        <4>. QED BY <4>1, <4>2, <4>3
      <3>. QED BY <3>1 DEF VInv2
    <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF VInv
  <1>. QED BY <1>1

THEOREM InductiveInvariance == VInv /\ [Next]_vars => VInv'
PROOF
  BY NextDef, StutterInv, IncreaseMaxBalInv, VoteForInv DEF BallotAction

THEOREM VT2 == Spec => []VInv
PROOF
  BY InitImpliesInv, InductiveInvariance, PTL DEF Spec
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
