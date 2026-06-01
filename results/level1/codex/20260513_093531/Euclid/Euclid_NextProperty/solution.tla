-------------------- MODULE Euclid_NextProperty --------------------
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

THEOREM InitProperty == Init => InductiveInvariant
  PROOF OMITTED

-------------------------------------------------------
AXIOM GCDProperty1 == \A p \in Number : GCD(p, p) = p
AXIOM GCDProperty2 == \A p, q \in Number : GCD(p, q) = GCD(q, p)
AXIOM GCDProperty3 == \A p, q \in Number : (p < q) => GCD(p, q) = GCD(p, q-p)
-------------------------------------------------------
THEOREM NextProperty == InductiveInvariant /\ Next => InductiveInvariant'
PROOF
  <1>1. ASSUME InductiveInvariant /\ Next
        PROVE InductiveInvariant'
    <2>1. x \in Number /\ y \in Number /\ GCD(x, y) = GCD(M, N)
      BY <1>1 DEF InductiveInvariant
    <2>2. CASE x < y /\ y' = y - x /\ x' = x
      <3>2. x' \in Number
        BY <2>1, <2>2 DEF Number
      <3>3. y' \in Number
        BY <2>1, <2>2 DEF Number
      <3>4. GCD(x', y') = GCD(M, N)
        BY <2>1, <2>2, GCDProperty3 DEF Number
      <3>. QED BY <3>2, <3>3, <3>4 DEF InductiveInvariant
    <2>3. CASE y < x /\ x' = x - y /\ y' = y
      <3>2. x' \in Number
        BY <2>1, <2>3 DEF Number
      <3>3. y' \in Number
        BY <2>1, <2>3 DEF Number
      <3>4. GCD(y, x) = GCD(y, x-y)
        BY <2>1, <2>3, GCDProperty3 DEF Number
      <3>5. GCD(x, y) = GCD(y, x)
        BY <2>1, GCDProperty2 DEF Number
      <3>6. x-y \in Number
        BY <2>3, <3>2
      <3>7. GCD(y, x-y) = GCD(x-y, y)
        BY <2>1, <3>6, GCDProperty2 DEF Number
      <3>8. GCD(x', y') = GCD(M, N)
        BY <2>1, <2>3, <3>4, <3>5, <3>7
      <3>. QED BY <3>2, <3>3, <3>8 DEF InductiveInvariant
    <2>. QED BY <1>1, <2>2, <2>3 DEF Next
  <1>. QED BY <1>1

=======================================================
