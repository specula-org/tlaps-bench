-------------------- MODULE Euclid_Correctness --------------------
EXTENDS Integers, TLAPS
-------------------------------------------------------
p | q == \E d \in 1..q : q = p * d
Divisors(q) == {d \in 1..q : d | q}
Maximum(S) == CHOOSE x \in S : \A y \in S : x \geq y
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))
Number == Nat \ {0}
-------------------------------------------------------
CONSTANTS M, N
VARIABLES x, y

ASSUME NumberAssumption == M \in Number /\ N \in Number
-------------------------------------------------------
Init == (x = M) /\ (y = N)

Next == \/ /\ x < y
           /\ y' = y - x
           /\ x' = x
        \/ /\ y < x
           /\ x' = x-y
           /\ y' = y

Spec == Init /\ [][Next]_<<x,y>>
-------------------------------------------------------
ResultCorrect == (x = y) => x = GCD(M, N)

InductiveInvariant ==
  /\ x \in Number
  /\ y \in Number
  /\ GCD(x, y) = GCD(M, N)
-------------------------------------------------------
USE DEF Number

-------------------------------------------------------
AXIOM GCDProperty1 == \A p \in Number : GCD(p, p) = p
AXIOM GCDProperty2 == \A p, q \in Number : GCD(p, q) = GCD(q, p)
AXIOM GCDProperty3 == \A p, q \in Number : (p < q) => GCD(p, q) = GCD(p, q-p)
-------------------------------------------------------
-------------------------------------------------------
LEMMA InductiveInvariantHolds == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
  BY NumberAssumption DEF Init, InductiveInvariant
<1>2. InductiveInvariant /\ [Next]_<<x,y>> => InductiveInvariant'
  <2> SUFFICES ASSUME InductiveInvariant, [Next]_<<x,y>>
               PROVE InductiveInvariant'
    OBVIOUS
  <2> USE DEF InductiveInvariant
  <2>1. CASE /\ x < y /\ y' = y - x /\ x' = x
    <3>1. x' \in Number BY <2>1
    <3>2. y' \in Number BY <2>1
    <3>3. GCD(x', y') = GCD(M, N)
      BY <2>1, GCDProperty3
    <3>4. QED BY <3>1, <3>2, <3>3
  <2>2. CASE /\ y < x /\ x' = x - y /\ y' = y
    <3>1. x' \in Number BY <2>2
    <3>2. y' \in Number BY <2>2
    <3>3. GCD(x', y') = GCD(M, N)
      BY <2>2, GCDProperty2, GCDProperty3
    <3>4. QED BY <3>1, <3>2, <3>3
  <2>3. CASE UNCHANGED <<x,y>>
    BY <2>3
  <2>4. QED BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

LEMMA InvImpliesResult == InductiveInvariant => ResultCorrect
  BY GCDProperty1 DEF InductiveInvariant, ResultCorrect
-------------------------------------------------------
THEOREM Correctness == Spec => []ResultCorrect
<1>1. Spec => []InductiveInvariant
  BY InductiveInvariantHolds
<1>2. InductiveInvariant => ResultCorrect
  BY InvImpliesResult
<1>3. QED
  BY <1>1, <1>2, PTL
=======================================================