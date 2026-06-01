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

THEOREM InitProperty == Init => InductiveInvariant
  PROOF OMITTED

-------------------------------------------------------
AXIOM GCDProperty1 == \A p \in Number : GCD(p, p) = p
AXIOM GCDProperty2 == \A p, q \in Number : GCD(p, q) = GCD(q, p)
AXIOM GCDProperty3 == \A p, q \in Number : (p < q) => GCD(p, q) = GCD(p, q-p)
-------------------------------------------------------
THEOREM NextProperty == InductiveInvariant /\ Next => InductiveInvariant'
  PROOF OMITTED

-------------------------------------------------------
THEOREM Correctness == Spec => []ResultCorrect
PROOF
  <1>1. Init => InductiveInvariant
    BY InitProperty
  <1>2. InductiveInvariant /\ [Next]_<<x,y>> => InductiveInvariant'
    BY NextProperty DEF InductiveInvariant
  <1>3. InductiveInvariant => ResultCorrect
    BY GCDProperty1 DEF InductiveInvariant, ResultCorrect
  <1>4. InductiveInvariant /\ [][Next]_<<x,y>> => []InductiveInvariant
    BY <1>2, PTL
  <1>5. Spec => []InductiveInvariant
    BY <1>1, <1>4 DEF Spec
  <1>6. QED
    BY <1>3, <1>5, PTL DEF Spec

=======================================================
