-------------------------------- MODULE Sets_PigeonHole --------------------------------
EXTENDS Integers, NaturalsInduction, TLAPS

IsBijection(f, S, T) == /\ f \in [S -> T]
                        /\ \A x, y \in S : (x # y) => (f[x] # f[y])
                        /\ \A y \in T : \E x \in S : f[x] = y

IsFiniteSet(S) == \E n \in Nat : \E f : IsBijection(f, 1..n, S)

CONSTANT Cardinality(_)
AXIOM CardinalityAxiom ==
         \A S : IsFiniteSet(S) =>
           \A n : (n = Cardinality(S)) <=>
                    (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
-----------------------------------------------------------------------------

------------------------------------------------------------------

PHQ(N) ==
  \A M \in Nat : \A h \in [1..N -> 1..M] :
    M < N => \E i, j \in 1..N : i # j /\ h[i] = h[j]

LEMMA IntervalPigeonHole ==
  ASSUME NEW n \in Nat, NEW m \in Nat, m < n,
         NEW g \in [1..n -> 1..m]
  PROVE  \E i, j \in 1..n : i # j /\ g[i] = g[j]
PROOF
  <1>1. PHQ(0)
    <2> SUFFICES ASSUME NEW M \in Nat, NEW h \in [1..0 -> 1..M], M < 0
                 PROVE  \E i, j \in 1..0 : i # j /\ h[i] = h[j]
      BY DEF PHQ
    <2> 0 \in Nat OBVIOUS
    <2> QED OBVIOUS
  <1>2. ASSUME NEW N \in Nat, PHQ(N)
        PROVE  PHQ(N+1)
    <2>HIH. \A MM \in Nat : \A hh \in [1..N -> 1..MM] :
              MM < N => \E i, j \in 1..N : i # j /\ hh[i] = hh[j]
      BY <1>2 DEF PHQ
    <2> SUFFICES ASSUME NEW M \in Nat, NEW h \in [1..(N+1) -> 1..M], M < N+1
                 PROVE  \E i, j \in 1..(N+1) : i # j /\ h[i] = h[j]
      BY DEF PHQ
    <2>1. CASE M = 0
      <3>a. 1 \in 1..(N+1) OBVIOUS
      <3>b. h[1] \in 1..M BY <3>a
      <3>c. 1..M = {} BY <2>1
      <3> QED BY <3>b, <3>c
    <2>2. CASE M >= 1
      <3>a. M - 1 \in Nat BY <2>2
      <3>b. N+1 \in 1..(N+1) OBVIOUS
      <3>c. h[N+1] \in 1..M BY <3>b
      <3> DEFINE p == h[N+1]
      <3>d. p \in 1..M BY <3>c
      <3>e. p \in Nat /\ p \in Int BY <3>d
      <3>f. p >= 1 /\ p <= M BY <3>d
      <3>3. CASE \E i \in 1..N : h[i] = p
        <4> PICK ii \in 1..N : h[ii] = p BY <3>3
        <4>a. ii \in 1..(N+1) /\ N+1 \in 1..(N+1) OBVIOUS
        <4>b. ii # N+1 OBVIOUS
        <4>c. h[ii] = h[N+1] OBVIOUS
        <4> QED BY <4>a, <4>b, <4>c
      <3>4. CASE \A i \in 1..N : h[i] # p
        <4>a. \A i \in 1..N : h[i] \in 1..M
          BY 1..N \subseteq 1..(N+1)
        <4>b. \A i \in 1..N : h[i] # p
          BY <3>4
        <4> DEFINE h2 == [i \in 1..N |-> IF h[i] < p THEN h[i] ELSE h[i] - 1]
        <4>1. h2 \in [1..N -> 1..(M-1)]
          <5> SUFFICES ASSUME NEW i \in 1..N
                       PROVE  h2[i] \in 1..(M-1)
            BY DEF h2
          <5>x. h[i] \in 1..M BY <4>a
          <5>y. h[i] # p BY <4>b
          <5>z. h[i] \in Nat /\ h[i] \in Int BY <5>x
          <5>I. CASE h[i] < p
            <6>a. h2[i] = h[i] BY <5>I, Zenon DEF h2
            <6>b. h[i] >= 1 BY <5>x
            <6>c. h[i] <= p-1 BY <5>I, <5>z, <3>e
            <6>d. p-1 <= M-1 BY <3>f, <3>e
            <6>e. h[i] <= M-1 BY <6>c, <6>d
            <6>f. M-1 \in Nat /\ M-1 \in Int BY <3>a
            <6> QED BY <6>a, <6>b, <6>e, <6>f
          <5>II. CASE ~(h[i] < p)
            <6>a. h[i] >= p BY <5>II, <5>z, <3>e
            <6>b. h[i] > p BY <6>a, <5>y, <5>z, <3>e
            <6>c. h2[i] = h[i] - 1 BY <5>II, Zenon DEF h2
            <6>d. h[i] >= p+1 BY <6>b, <5>z, <3>e
            <6>e. h[i] - 1 >= p BY <6>d, <5>z, <3>e
            <6>f. p >= 1 BY <3>f
            <6>g. h[i] - 1 >= 1 BY <6>e, <6>f
            <6>h. h[i] <= M BY <5>x
            <6>i. h[i] - 1 <= M-1 BY <6>h, <5>z
            <6>j. M-1 \in Nat /\ M-1 \in Int BY <3>a
            <6> QED BY <6>c, <6>g, <6>i, <6>j
          <5> QED BY <5>I, <5>II
        <4>2. M-1 < N
          <5>a. M < N+1 OBVIOUS
          <5>b. M \in Int /\ N \in Int OBVIOUS
          <5> QED BY <5>a, <5>b
        <4>3. \E i, j \in 1..N : i # j /\ h2[i] = h2[j]
          <5>a. M-1 \in Nat BY <3>a
          <5>b. M-1 < N BY <4>2
          <5>c. h2 \in [1..N -> 1..(M-1)] BY <4>1
          <5> QED BY <2>HIH, <5>a, <5>b, <5>c
        <4>4. PICK ii, jj \in 1..N : ii # jj /\ h2[ii] = h2[jj]
          BY <4>3
        <4>5. h[ii] = h[jj]
          <5>a. ii \in 1..N /\ jj \in 1..N BY <4>4
          <5>x. h[ii] \in 1..M /\ h[ii] # p BY <5>a, <4>a, <4>b
          <5>y. h[jj] \in 1..M /\ h[jj] # p BY <5>a, <4>a, <4>b
          <5>z. h[ii] \in Int /\ h[jj] \in Int BY <5>x, <5>y
          <5>c. h2[ii] = IF h[ii] < p THEN h[ii] ELSE h[ii] - 1
            BY <5>a, Zenon DEF h2
          <5>d. h2[jj] = IF h[jj] < p THEN h[jj] ELSE h[jj] - 1
            BY <5>a, Zenon DEF h2
          <5>I. CASE h[ii] < p /\ h[jj] < p
            <6>a. h2[ii] = h[ii] BY <5>I, <5>c
            <6>b. h2[jj] = h[jj] BY <5>I, <5>d
            <6> QED BY <4>4, <6>a, <6>b
          <5>II. CASE h[ii] < p /\ ~(h[jj] < p)
            <6>a. h[jj] >= p BY <5>II, <5>z, <3>e
            <6>b. h[jj] > p BY <6>a, <5>y, <5>z, <3>e
            <6>c. h2[ii] = h[ii] BY <5>II, <5>c
            <6>d. h2[jj] = h[jj] - 1 BY <5>II, <5>d
            <6>e. h[ii] <= p - 1 BY <5>II, <5>z, <3>e
            <6>f. h[jj] - 1 >= p BY <6>b, <5>z, <3>e
            <6>g. h[ii] < h[jj] - 1 BY <6>e, <6>f, <3>e, <5>z
            <6>h. h2[ii] # h2[jj] BY <6>c, <6>d, <6>g, <5>z
            <6> QED BY <4>4, <6>h
          <5>III. CASE ~(h[ii] < p) /\ h[jj] < p
            <6>a. h[ii] >= p BY <5>III, <5>z, <3>e
            <6>b. h[ii] > p BY <6>a, <5>x, <5>z, <3>e
            <6>c. h2[ii] = h[ii] - 1 BY <5>III, <5>c
            <6>d. h2[jj] = h[jj] BY <5>III, <5>d
            <6>e. h[jj] <= p - 1 BY <5>III, <5>z, <3>e
            <6>f. h[ii] - 1 >= p BY <6>b, <5>z, <3>e
            <6>g. h[jj] < h[ii] - 1 BY <6>e, <6>f, <3>e, <5>z
            <6>h. h2[ii] # h2[jj] BY <6>c, <6>d, <6>g, <5>z
            <6> QED BY <4>4, <6>h
          <5>IV. CASE ~(h[ii] < p) /\ ~(h[jj] < p)
            <6>a. h[ii] >= p BY <5>IV, <5>z, <3>e
            <6>b. h[ii] > p BY <6>a, <5>x, <5>z, <3>e
            <6>c. h[jj] >= p BY <5>IV, <5>z, <3>e
            <6>d. h[jj] > p BY <6>c, <5>y, <5>z, <3>e
            <6>e. h2[ii] = h[ii] - 1 BY <5>IV, <5>c
            <6>f. h2[jj] = h[jj] - 1 BY <5>IV, <5>d
            <6>g. h[ii] - 1 = h[jj] - 1 BY <4>4, <6>e, <6>f
            <6> QED BY <6>g, <5>z
          <5> QED BY <5>I, <5>II, <5>III, <5>IV
        <4>6. ii \in 1..(N+1) /\ jj \in 1..(N+1)
          <5>a. ii \in 1..N /\ jj \in 1..N BY <4>4
          <5> QED BY <5>a
        <4>7. ii # jj BY <4>4
        <4> QED BY <4>5, <4>6, <4>7
      <3> QED BY <3>3, <3>4
    <2> QED BY <2>1, <2>2
  <1>3. \A N \in Nat : PHQ(N)
    BY <1>1, <1>2, NatInduction, Isa
  <1>4. PHQ(n) BY <1>3
  <1> QED BY <1>4 DEF PHQ
------------------------------------------------------------------

------------------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

-----------------------------------------------------------------------------

THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
PROOF
  <1> SUFFICES ASSUME NEW S, NEW T,
                      IsFiniteSet(S), IsFiniteSet(T),
                      Cardinality(T) < Cardinality(S),
                      NEW f \in [S -> T]
               PROVE  \E x, y \in S : x # y /\ f[x] = f[y]
    OBVIOUS
  <1>1. Cardinality(S) \in Nat /\ \E aa : IsBijection(aa, 1..Cardinality(S), S)
    <2> Cardinality(S) = Cardinality(S) OBVIOUS
    <2> QED BY CardinalityAxiom
  <1>2. Cardinality(T) \in Nat /\ \E bb : IsBijection(bb, 1..Cardinality(T), T)
    <2> Cardinality(T) = Cardinality(T) OBVIOUS
    <2> QED BY CardinalityAxiom
  <1>3. PICK alpha : IsBijection(alpha, 1..Cardinality(S), S) BY <1>1
  <1>4. PICK beta : IsBijection(beta, 1..Cardinality(T), T) BY <1>2
  <1> DEFINE k == Cardinality(S)
  <1> DEFINE m == Cardinality(T)
  <1>5. k \in Nat /\ m \in Nat /\ m < k BY <1>1, <1>2
  <1>6. alpha \in [1..k -> S]
        /\ (\A x, y \in 1..k : (x # y) => (alpha[x] # alpha[y]))
        /\ (\A y \in S : \E x \in 1..k : alpha[x] = y)
    BY <1>3 DEF IsBijection
  <1>7. beta \in [1..m -> T]
        /\ (\A x, y \in 1..m : (x # y) => (beta[x] # beta[y]))
        /\ (\A y \in T : \E x \in 1..m : beta[x] = y)
    BY <1>4 DEF IsBijection
  <1> DEFINE g == [i \in 1..k |-> CHOOSE j \in 1..m : beta[j] = f[alpha[i]]]
  <1>8. g \in [1..k -> 1..m]
    <2> SUFFICES ASSUME NEW i \in 1..k
                 PROVE  (CHOOSE j \in 1..m : beta[j] = f[alpha[i]]) \in 1..m
      BY DEF g
    <2>a. alpha[i] \in S BY <1>6
    <2>b. f[alpha[i]] \in T BY <2>a
    <2>c. \E j \in 1..m : beta[j] = f[alpha[i]] BY <2>b, <1>7
    <2> QED BY <2>c
  <1>9. PICK ii, jj \in 1..k : ii # jj /\ g[ii] = g[jj]
    BY <1>5, <1>8, IntervalPigeonHole
  <1>10. alpha[ii] \in S /\ alpha[jj] \in S
    BY <1>6, <1>9
  <1>11. alpha[ii] # alpha[jj]
    BY <1>6, <1>9
  <1>12. g[ii] \in 1..m /\ g[jj] \in 1..m
    BY <1>8, <1>9
  <1>13. beta[g[ii]] = f[alpha[ii]]
    <2>a. ii \in 1..k BY <1>9
    <2>b. alpha[ii] \in S BY <1>6, <2>a
    <2>c. f[alpha[ii]] \in T BY <2>b
    <2>d. \E j \in 1..m : beta[j] = f[alpha[ii]] BY <2>c, <1>7
    <2>e. g[ii] = CHOOSE j \in 1..m : beta[j] = f[alpha[ii]]
      BY <2>a DEF g
    <2>f. beta[CHOOSE j \in 1..m : beta[j] = f[alpha[ii]]] = f[alpha[ii]]
      BY <2>d
    <2> QED BY <2>e, <2>f
  <1>14. beta[g[jj]] = f[alpha[jj]]
    <2>a. jj \in 1..k BY <1>9
    <2>b. alpha[jj] \in S BY <1>6, <2>a
    <2>c. f[alpha[jj]] \in T BY <2>b
    <2>d. \E j \in 1..m : beta[j] = f[alpha[jj]] BY <2>c, <1>7
    <2>e. g[jj] = CHOOSE j \in 1..m : beta[j] = f[alpha[jj]]
      BY <2>a DEF g
    <2>f. beta[CHOOSE j \in 1..m : beta[j] = f[alpha[jj]]] = f[alpha[jj]]
      BY <2>d
    <2> QED BY <2>e, <2>f
  <1>15. f[alpha[ii]] = f[alpha[jj]]
    BY <1>9, <1>13, <1>14
  <1> QED BY <1>10, <1>11, <1>15
-------------------------------------------------------

=============================================================================
