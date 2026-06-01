----------------------------- MODULE VoteProof_VT1 ------------------------------

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

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}
-----------------------------------------------------------------------------

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
           VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
                  VotedFor(a, b, v) => SafeAt(b, v)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Weak natural-number induction (predicate form), derived from the        *)
(* function-form SimpleNatInduction axiom.                                 *)
(***************************************************************************)
LEMMA NatInduction ==
  ASSUME NEW P(_),
         P(0),
         \A n \in Nat : P(n) => P(n+1)
  PROVE  \A n \in Nat : P(n)
PROOF
<1> DEFINE f == [n \in Nat |-> P(n)]
<1>a. \A n \in Nat : f[n] = P(n)  OBVIOUS
<1>1. f[0]  BY <1>a
<1>2. \A n \in Nat : f[n] => f[n+1]  BY <1>a
<1>3. \A n \in Nat : f[n]  BY <1>1, <1>2, SimpleNatInduction
<1> QED  BY <1>3, <1>a

(***************************************************************************)
(* Strong (course-of-values) natural-number induction.                     *)
(***************************************************************************)
LEMMA GeneralNatInduction ==
  ASSUME NEW P(_),
         \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
  PROVE  \A n \in Nat : P(n)
PROOF
<1> DEFINE Q(n) == \A m \in 0..n : P(m)
<1> DEFINE g == [n \in Nat |-> Q(n)]
<1>a. \A n \in Nat : g[n] = Q(n)  OBVIOUS
<1>1. g[0]
  <2>1. 0..(0-1) = {}  BY SMT
  <2>2. P(0)  BY <2>1
  <2>3. Q(0)  BY <2>2
  <2> QED  BY <2>3, <1>a
<1>2. \A n \in Nat : g[n] => g[n+1]
  <2> SUFFICES ASSUME NEW n \in Nat, Q(n)
               PROVE  Q(n+1)
    BY <1>a
  <2>1. \A m \in 0..(n+1-1) : P(m)  BY DEF Q
  <2>2. P(n+1)  BY <2>1
  <2>3. \A m \in 0..n : P(m)  BY DEF Q
  <2> QED  BY <2>2, <2>3, SMT
<1>3. \A n \in Nat : g[n]  BY <1>1, <1>2, SimpleNatInduction
<1>4. \A n \in Nat : Q(n)  BY <1>3, <1>a
<1> QED  BY <1>4

(***************************************************************************)
(* A recursively defined function over the naturals is well defined when   *)
(* f[n] depends only on the values of f at arguments smaller than n.       *)
(* This is a self-contained replica of the standard-library theorem        *)
(* RecursiveFcnOfNat, proved here from the induction lemmas above.         *)
(***************************************************************************)
LEMMA RecursiveFcnOfNat ==
  ASSUME NEW Def(_,_),
         ASSUME NEW n \in Nat, NEW g, NEW h,
                \A i \in 0..(n-1) : g[i] = h[i]
         PROVE  Def(g, n) = Def(h, n)
  PROVE  LET f[n \in Nat] == Def(f, n)
         IN  f = [n \in Nat |-> Def(f, n)]
PROOF
<1>. SUFFICES \E ff : ff = [n \in Nat |-> Def(ff, n)]
  OBVIOUS
<1>. DEFINE F[n \in Nat] == [i \in 0 .. n-1 |-> Def(F[n-1], i)]
            f[n \in Nat] == F[n+1][n]
<1>1. F = [n \in Nat |-> [i \in 0 .. n-1 |-> Def(F[n-1], i)]]
  <2>. SUFFICES \E FF : FF = [n \in Nat |-> [i \in 0 .. n-1 |-> Def(FF[n-1], i)]]
    BY Zenon
  <2>. DEFINE P(gg,k) == gg = [n \in 0 .. k |-> [i \in 0 .. n-1 |-> Def(gg[n-1], i)]]
              G(k) == CHOOSE gg : P(gg,k)
              FF == [n \in Nat |-> [i \in 0 .. n-1 |-> G(n)[n][i] ]]
  <2>0. ASSUME NEW gg, NEW k \in Nat, P(gg,k),
               NEW n \in 0 .. k, NEW i \in 0 .. n-1
        PROVE  gg[n][i] = Def(gg[n-1], i)
    <3>. DEFINE ggg == [m \in 0 .. k |-> [j \in 0 .. m-1 |-> Def(gg[m-1], j)]]
    <3>1. ggg[n][i] = Def(gg[n-1],i)  OBVIOUS
    <3>2. gg = ggg  BY <2>0, Zenon
    <3>. QED  BY <3>1, <3>2, Zenon
  <2>1. \A k \in Nat : \E gg : P(gg,k)
    <3>. DEFINE Q(k) == \E gg : P(gg,k)
    <3>. SUFFICES \A k \in Nat : Q(k)  BY Zenon
    <3>1. Q(0)
      <4>. DEFINE g0 == [n \in {0} |-> [i \in {} |-> {}]]
      <4>1. P(g0, 0)  BY Isa
      <4>. QED  BY <4>1, Zenon
    <3>2. ASSUME NEW k \in Nat, Q(k)
          PROVE  Q(k+1)
      <4>1. PICK gg : P(gg,k)  BY <3>2, Zenon
      <4>1a. ASSUME NEW n \in 0 .. k, NEW i \in 0 .. n-1
             PROVE  gg[n][i] = Def(gg[n-1], i)
        BY <4>1, <2>0, Zenon
      <4>. DEFINE hh == [n \in 0 .. k+1 |-> [i \in 0 .. n-1 |-> Def(gg[n-1], i) ]]
      <4>2. hh = [n \in 0 .. k+1 |-> [i \in 0 .. n-1 |-> Def(hh[n-1], i)]]
        <5>. SUFFICES ASSUME NEW n \in 0 .. k+1, NEW i \in 0 .. n-1
                      PROVE  hh[n][i] = Def(hh[n-1], i)
          BY Zenon
        <5>1. hh[n][i] = Def(gg[n-1], i)  OBVIOUS
        <5>2. ASSUME NEW j \in 0 .. i-1
              PROVE  gg[n-1][j] = hh[n-1][j]
          BY <4>1a
        <5>. HIDE DEF hh
        <5>3. Def(gg[n-1],i) = Def(hh[n-1],i)  BY <5>2
        <5>. QED  BY <5>1, <5>3
      <4>. HIDE DEF hh
      <4>. QED  BY <4>2, Zenon
    <3>. HIDE DEF Q
    <3>. QED  BY <3>1, <3>2, NatInduction, IsaM("blast")
  <2>2. \A k \in Nat : P(G(k), k)  BY <2>1, Zenon
  <2>3. \A k \in Nat : \A l \in 0 .. k : \A i \in 0 .. l-1 : \A gg,hh :
           P(gg,k) /\ P(hh,l) => gg[l][i] = hh[l][i]
    <3>. DEFINE Q(k) == \A l \in 0 .. k : \A i \in 0 .. l-1 : \A gg,hh :
                           P(gg,k) /\ P(hh,l) => gg[l][i] = hh[l][i]
    <3>. SUFFICES \A k \in Nat : Q(k)  BY Zenon
    <3>0. Q(0)  OBVIOUS
    <3>1. ASSUME NEW k \in Nat, Q(k)
          PROVE  Q(k+1)
      <4>. HIDE DEF P
      <4>. SUFFICES ASSUME NEW l \in 1 .. k+1, NEW i \in 0 .. l-1, NEW gg, NEW hh,
                           P(gg,k+1), P(hh,l)
                    PROVE  gg[l][i] = hh[l][i]
        OBVIOUS
      <4>1. /\ gg[l][i] = Def(gg[l-1],i)
            /\ hh[l][i] = Def(hh[l-1],i)
        BY <2>0
      <4>. DEFINE gp == [nn \in 0 .. k |-> [ii \in 0 .. nn-1 |-> Def(gg[nn-1],ii)]]
                  hp == [nn \in 0 .. l-1 |-> [ii \in 0 .. nn-1 |-> Def(hh[nn-1],ii)]]
      <4>2. P(gp,k)
        <5>1. ASSUME NEW nn \in 0 .. k, NEW j \in 0 .. nn-1
              PROVE  gp[nn-1] = gg[nn-1]
          <6>1. gp[nn-1] = [ii \in 0 .. nn-2 |-> Def(gg[nn-2],ii)]
            OBVIOUS
          <6>2. gg[nn-1] = [ii \in 0 .. (nn-1)-1 |-> Def(gg[(nn-1)-1],ii)]
            BY nn-1 \in 0 .. k, nn-1 \in 0 .. k+1, Zenon DEF P
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY <5>1, Zenon DEF P
      <4>3. P(hp,l-1)
        <5>1. ASSUME NEW nn \in 0 .. l-1, NEW j \in 0 .. nn-1
              PROVE  hp[nn-1] = hh[nn-1]
          <6>1. hp[nn-1] = [ii \in 0 .. nn-2 |-> Def(hh[nn-2],ii)]
            OBVIOUS
          <6>2. hh[nn-1] = [ii \in 0 .. (nn-1)-1 |-> Def(hh[(nn-1)-1],ii)]
            BY nn-1 \in 0 .. l-1, nn-1 \in 0 .. l, Zenon DEF P
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY <5>1, Zenon DEF P
      <4>4. ASSUME NEW m \in 0 .. i-1
            PROVE  gp[l-1][m] = hp[l-1][m]
        <5>. HIDE DEF gp, hp
        <5>. QED  BY <3>1, <4>2, <4>3, l-1 \in 0 .. k, m \in 0 .. (l-1)-1
      <4>5. \A m \in 0 .. i-1 : gg[l-1][m] = gp[l-1][m]   BY <2>0
      <4>6. \A m \in 0 .. i-1 : hh[l-1][m] = hp[l-1][m]   BY <2>0
      <4>7. \A m \in 0 .. i-1 : gg[l-1][m] = hh[l-1][m]   BY <4>4, <4>5, <4>6, Zenon
      <4>8. Def(gg[l-1],i) = Def(hh[l-1],i)               BY <4>7
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
<1>. DEFINE Pp(n) == \A m \in 0 .. n : \A i \in 0 .. m-1 : F[n][i] = F[m][i]
<1>3. \A n \in Nat : Pp(n)
  <2>1. ASSUME NEW n \in Nat, \A k \in 0 .. n-1 : Pp(k)
        PROVE  Pp(n)
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
  <2>. HIDE DEF Pp
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

(***************************************************************************)
(* The body of the recursive definition of SafeAt, as a top-level operator.*)
(***************************************************************************)
SafeAtBody(g, vv, bb) ==
  \/ bb = 0
  \/ \E Q \in Quorum :
       /\ \A a \in Q : maxBal[a] \geq bb
       /\ \E c \in -1..(bb-1) :
            /\ (c # -1) => /\ g[c]
                           /\ \A a \in Q :
                                \A w \in Value :
                                   VotedFor(a, c, w) => (w = vv)
            /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)

(***************************************************************************)
(* SafeAtBody(g, vv, bb) depends on g only through g[c] for c < bb.        *)
(***************************************************************************)
LEMMA SafeAtBodyCong ==
  ASSUME NEW vv \in Value, NEW bb \in Nat, NEW g, NEW h,
         \A i \in 0..(bb-1) : g[i] = h[i]
  PROVE  SafeAtBody(g, vv, bb) = SafeAtBody(h, vv, bb)
PROOF
<1> DEFINE Cl(ff, Q, c) ==
      /\ (c # -1) => /\ ff[c]
                     /\ \A a \in Q :
                          \A w \in Value : VotedFor(a, c, w) => (w = vv)
      /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
<1>1. \A Q \in Quorum, c \in -1..(bb-1) : Cl(g, Q, c) = Cl(h, Q, c)
  <2> SUFFICES ASSUME NEW Q \in Quorum, NEW c \in -1..(bb-1)
               PROVE  Cl(g, Q, c) = Cl(h, Q, c)
    OBVIOUS
  <2>1. CASE c = -1  BY <2>1
  <2>2. CASE c # -1
    <3>1. c \in 0..(bb-1)  BY <2>2
    <3>2. g[c] = h[c]  BY <3>1
    <3> QED  BY <3>2
  <2> QED  BY <2>1, <2>2
<1> QED  BY <1>1 DEF SafeAtBody

(***************************************************************************)
(* One-step (forward) unfolding of the recursive definition of SafeAt.     *)
(***************************************************************************)
LEMMA SafeAtUnfold ==
  ASSUME NEW b \in Ballot, NEW v \in Value, SafeAt(b, v), b # 0
  PROVE  \E Q \in Quorum :
           /\ \A a \in Q : maxBal[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)
                               /\ \A a \in Q :
                                    \A w \in Value :
                                       VotedFor(a, c, w) => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
PROOF
<1> USE DEF Ballot
<1> DEFINE D(g, bb) == SafeAtBody(g, v, bb)
<1>dep. ASSUME NEW nn \in Nat, NEW g, NEW h, \A i \in 0..(nn-1) : g[i] = h[i]
        PROVE  D(g, nn) = D(h, nn)
  BY <1>dep, SafeAtBodyCong
<1> HIDE DEF D
<1> DEFINE SA[bb \in Nat] == D(SA, bb)
<1>rec. SA = [bb \in Nat |-> D(SA, bb)]
  BY <1>dep, RecursiveFcnOfNat, Isa
<1> USE DEF D
<1>sa. \A bb \in Nat : SafeAt(bb, v) = SA[bb]
  BY DEF SafeAt, SafeAtBody, D
<1>ap. SafeAtBody(SA, v, b)
  <2>1. SafeAt(b, v) = SA[b]  BY <1>sa
  <2>2. SA[b] = SafeAtBody(SA, v, b)  BY <1>rec DEF D
  <2> QED  BY <2>1, <2>2
<1>2. \E Q \in Quorum :
        /\ \A a \in Q : maxBal[a] \geq b
        /\ \E c \in -1..(b-1) :
             /\ (c # -1) => /\ SA[c]
                            /\ \A a \in Q :
                                 \A w \in Value :
                                    VotedFor(a, c, w) => (w = v)
             /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
  BY <1>ap DEF SafeAtBody
<1> HIDE DEF SA
<1> QED
  <2>p. PICK Q \in Quorum :
          /\ \A a \in Q : maxBal[a] \geq b
          /\ \E c \in -1..(b-1) :
               /\ (c # -1) => /\ SA[c]
                              /\ \A a \in Q :
                                   \A w \in Value :
                                      VotedFor(a, c, w) => (w = v)
               /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
    BY <1>2
  <2>c. PICK c \in -1..(b-1) :
          /\ (c # -1) => /\ SA[c]
                         /\ \A a \in Q :
                              \A w \in Value :
                                 VotedFor(a, c, w) => (w = v)
          /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
    BY <2>p
  <2>g. (c # -1) => /\ SafeAt(c, v)
                    /\ \A a \in Q :
                         \A w \in Value :
                            VotedFor(a, c, w) => (w = v)
    <3> SUFFICES ASSUME c # -1
                 PROVE  /\ SafeAt(c, v)
                        /\ \A a \in Q :
                             \A w \in Value :
                                VotedFor(a, c, w) => (w = v)
      OBVIOUS
    <3>1. /\ SA[c]
          /\ \A a \in Q :
               \A w \in Value : VotedFor(a, c, w) => (w = v)
      BY <2>c
    <3>2. c \in 0..(b-1)  BY <2>c
    <3>3. SafeAt(c, v) = SA[c]  BY <1>sa, <3>2
    <3> QED  BY <3>1, <3>3
  <2> QED  BY <2>p, <2>c, <2>g

(***************************************************************************)
(* If a value is chosen at a ballot, any other value chosen at the same     *)
(* ballot is equal to it (one vote per ballot per acceptor).               *)
(***************************************************************************)
LEMMA ChosenInUnique ==
  ASSUME VInv1, NEW b \in Ballot, NEW v \in Value, NEW w \in Value,
         ChosenIn(b, v), ChosenIn(b, w)
  PROVE  v = w
PROOF
<1>1. PICK Q1 \in Quorum : \A a \in Q1 : VotedFor(a, b, v)  BY DEF ChosenIn
<1>2. PICK Q2 \in Quorum : \A a \in Q2 : VotedFor(a, b, w)  BY DEF ChosenIn
<1>3. Q1 \cap Q2 # {}  BY QA
<1>4. PICK a \in Q1 \cap Q2 : TRUE  BY <1>3
<1>5. a \in Acceptor  BY <1>1, <1>4, QA
<1>6. VotedFor(a, b, v) /\ VotedFor(a, b, w)  BY <1>1, <1>2, <1>4
<1> QED  BY <1>5, <1>6 DEF VInv1

(***************************************************************************)
(* A chosen value is safe at its ballot.                                   *)
(***************************************************************************)
LEMMA ChosenImpliesSafe ==
  ASSUME VInv2, NEW b \in Ballot, NEW v \in Value, ChosenIn(b, v)
  PROVE  SafeAt(b, v)
PROOF
<1>1. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)  BY DEF ChosenIn
<1>2. Q # {}  BY QA
<1>3. PICK a \in Q : TRUE  BY <1>2
<1>4. a \in Acceptor  BY <1>1, <1>3, QA
<1>5. VotedFor(a, b, v)  BY <1>1, <1>3
<1> QED  BY <1>4, <1>5 DEF VInv2

(***************************************************************************)
(* The key inductive lemma: if w is safe at ballot c, then any value        *)
(* chosen at an earlier ballot b < c must equal w.  Proved by strong        *)
(* induction on c using the one-step unfolding of SafeAt.                  *)
(***************************************************************************)
LEMMA SafeImpliesEqual ==
  \A c \in Ballot : \A w \in Value :
    SafeAt(c, w) =>
      \A b \in 0..(c-1) : \A v \in Value : ChosenIn(b, v) => (v = w)
PROOF
<1> USE DEF Ballot
<1> DEFINE P(c) == \A w \in Value :
                     SafeAt(c, w) =>
                       \A b \in 0..(c-1) : \A v \in Value : ChosenIn(b, v) => (v = w)
<1> SUFFICES \A c \in Nat : P(c)  BY DEF P
<1>ind. ASSUME NEW c \in Nat, \A cc \in 0..(c-1) : P(cc)
        PROVE  P(c)
  <2> SUFFICES ASSUME NEW w \in Value, SafeAt(c, w),
                      NEW b \in 0..(c-1), NEW v \in Value, ChosenIn(b, v)
               PROVE  v = w
    BY DEF P
  <2>c0. c # 0  BY SMT
  <2>su. \E Q \in Quorum :
           /\ \A a \in Q : maxBal[a] \geq c
           /\ \E cc \in -1..(c-1) :
                /\ (cc # -1) => /\ SafeAt(cc, w)
                                /\ \A a \in Q :
                                     \A ww \in Value : VotedFor(a, cc, ww) => (ww = w)
                /\ \A d \in (cc+1)..(c-1), a \in Q : DidNotVoteIn(a, d)
    BY <2>c0, SafeAtUnfold
  <2>q. PICK Q \in Quorum :
          /\ \A a \in Q : maxBal[a] \geq c
          /\ \E cc \in -1..(c-1) :
               /\ (cc # -1) => /\ SafeAt(cc, w)
                               /\ \A a \in Q :
                                    \A ww \in Value : VotedFor(a, cc, ww) => (ww = w)
               /\ \A d \in (cc+1)..(c-1), a \in Q : DidNotVoteIn(a, d)
    BY <2>su
  <2>cc. PICK cc \in -1..(c-1) :
           /\ (cc # -1) => /\ SafeAt(cc, w)
                           /\ \A a \in Q :
                                \A ww \in Value : VotedFor(a, cc, ww) => (ww = w)
           /\ \A d \in (cc+1)..(c-1), a \in Q : DidNotVoteIn(a, d)
    BY <2>q
  <2>qb. PICK Qb \in Quorum : \A a \in Qb : VotedFor(a, b, v)  BY DEF ChosenIn
  <2>int. Q \cap Qb # {}  BY QA
  <2>aa. PICK aa \in Q \cap Qb : TRUE  BY <2>int
  <2>av. VotedFor(aa, b, v)  BY <2>qb, <2>aa
  <2>aQ. aa \in Q  BY <2>aa
  <2>ble. b <= cc
    <3>1. b \in 0..(c-1) /\ cc \in -1..(c-1)  BY <2>cc
    <3> SUFFICES ASSUME cc < b PROVE FALSE  BY <3>1, SMT
    <3>3. b \in (cc+1)..(c-1)  BY <3>1, SMT
    <3>4. DidNotVoteIn(aa, b)  BY <3>3, <2>aQ, <2>cc
    <3>5. ~ VotedFor(aa, b, v)  BY <3>4 DEF DidNotVoteIn
    <3> QED  BY <3>5, <2>av
  <2>ccp. cc # -1  BY <2>ble, <2>cc, SMT
  <2>safe. /\ SafeAt(cc, w)
           /\ \A a \in Q : \A ww \in Value : VotedFor(a, cc, ww) => (ww = w)
    BY <2>ccp, <2>cc
  <2>1. CASE b = cc
    <3>1. VotedFor(aa, cc, v)  BY <2>av, <2>1
    <3>2. \A ww \in Value : VotedFor(aa, cc, ww) => (ww = w)  BY <2>safe, <2>aQ
    <3> QED  BY <3>1, <3>2
  <2>2. CASE b < cc
    <3>1. cc \in 0..(c-1)  BY <2>ccp, <2>cc, SMT
    <3>2. P(cc)  BY <1>ind, <3>1
    <3>3. \A b2 \in 0..(cc-1) : \A v2 \in Value : ChosenIn(b2, v2) => (v2 = w)
      BY <3>2, <2>safe DEF P
    <3>4. b \in 0..(cc-1)  BY <2>2, <2>cc, SMT
    <3> QED  BY <3>3, <3>4
  <2> QED  BY <2>ble, <2>1, <2>2, SMT
<1> HIDE DEF P
<1> QED  BY ONLY <1>ind, GeneralNatInduction, Isa

THEOREM VT1 == /\ TypeOK
               /\ VInv1
               /\ VInv2
               => \A v, w :
                    (v \in chosen) /\ (w \in chosen) => (v = w)
PROOF
<1> USE DEF Ballot
<1> SUFFICES ASSUME TypeOK, VInv1, VInv2, NEW v, NEW w,
                    v \in chosen, w \in chosen
             PROVE  v = w
  OBVIOUS
<1>val. v \in Value /\ w \in Value  BY DEF chosen
<1>bv. PICK bv \in Ballot : ChosenIn(bv, v)  BY DEF chosen
<1>bw. PICK bw \in Ballot : ChosenIn(bw, w)  BY DEF chosen
<1>1. CASE bv = bw
  <2>1. ChosenIn(bv, w)  BY <1>bw, <1>1
  <2> QED  BY ChosenInUnique, <1>bv, <2>1, <1>val
<1>2. CASE bv < bw
  <2>1. SafeAt(bw, w)  BY ChosenImpliesSafe, <1>bw, <1>val
  <2>2. bv \in 0..(bw-1)  BY <1>2, <1>bv, <1>bw, SMT
  <2>3. \A b2 \in 0..(bw-1) : \A v2 \in Value : ChosenIn(b2, v2) => (v2 = w)
    BY <2>1, SafeImpliesEqual, <1>val, <1>bw
  <2> QED  BY <2>2, <2>3, <1>bv, <1>val
<1>3. CASE bw < bv
  <2>1. SafeAt(bv, v)  BY ChosenImpliesSafe, <1>bv, <1>val
  <2>2. bw \in 0..(bv-1)  BY <1>3, <1>bv, <1>bw, SMT
  <2>3. \A b2 \in 0..(bv-1) : \A v2 \in Value : ChosenIn(b2, v2) => (v2 = v)
    BY <2>1, SafeImpliesEqual, <1>val, <1>bv
  <2>4. w = v  BY <2>2, <2>3, <1>bw, <1>val
  <2> QED  BY <2>4
<1> QED  BY <1>1, <1>2, <1>3, <1>bv, <1>bw, SMT

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

ASSUME AcceptorNonempty == Acceptor # {}

-----------------------------------------------------------------------------

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

