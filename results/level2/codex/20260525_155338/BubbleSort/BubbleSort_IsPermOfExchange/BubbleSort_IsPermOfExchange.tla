----------------------------- MODULE BubbleSort_IsPermOfExchange -----------------------------

EXTENDS Integers, TLAPS, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat /\ N >= 1

-----------------------------------------------------------------------------

Perms == { f \in [1..N -> 1..N] : 
                     \A i \in 1..N : \E j \in 1..N : f[i] = f[j] }

f ** g == [i \in 1..N |-> f[g[i]]]
   
IsPermOf(A, B) == \E f \in Perms : A = (B ** f)

Exchange(A, i, j) == [A EXCEPT ![i] = A[j], ![j] = A[i]]

IndexExchange(i, j) ==
  [k \in 1..N |-> IF k = i THEN j ELSE IF k = j THEN i ELSE k]

LEMMA IndexExchangeInPerms ==
  ASSUME NEW i \in 1..N, NEW j \in 1..N
  PROVE  IndexExchange(i, j) \in Perms
BY SMT DEF IndexExchange, Perms

LEMMA ExchangeType ==
  ASSUME NEW A \in [1..N -> Int],
         NEW i \in 1..N,
         NEW j \in 1..N
  PROVE  Exchange(A, i, j) \in [1..N -> Int]
BY SMT DEF Exchange

LEMMA ExchangeComposition ==
  ASSUME NEW A \in [1..N -> Int],
         NEW i \in 1..N,
         NEW j \in 1..N
  PROVE  Exchange(A, i, j) = (A ** IndexExchange(i, j))
BY SMT DEF Exchange, IndexExchange, **

THEOREM IsPermOfExchange == 
           \A A \in [1..N -> Int],  i, j \in 1..N :
             /\ [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
             /\ IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
PROOF
<1>1. ASSUME NEW A \in [1..N -> Int],
             NEW i \in 1..N,
             NEW j \in 1..N
      PROVE  /\ [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
             /\ IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
  <2>1. [A EXCEPT ![i] = A[j], ![j] = A[i]] = Exchange(A, i, j)
    BY DEF Exchange
  <2>2. [A EXCEPT ![i] = A[j], ![j] = A[i]] \in [1..N -> Int]
    BY <1>1, <2>1, ExchangeType
  <2>3. IsPermOf([A EXCEPT ![i] = A[j], ![j] = A[i]], A)
    BY <1>1, <2>1, IndexExchangeInPerms, ExchangeComposition DEF IsPermOf
  <2>. QED BY <2>2, <2>3
<1>. QED BY <1>1

----------------------------------------------------------------------------

VARIABLES A, A0, i, j, pc

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
