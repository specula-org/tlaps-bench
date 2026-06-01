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

-------------------------------------------------------
USE DEF Number

-------------------------------------------------------
AXIOM GCDProperty1 == \A p \in Number : GCD(p, p) = p
AXIOM GCDProperty2 == \A p, q \in Number : GCD(p, q) = GCD(q, p)
AXIOM GCDProperty3 == \A p, q \in Number : (p < q) => GCD(p, q) = GCD(p, q-p)
-------------------------------------------------------
-------------------------------------------------------
IndInv == /\ x \in Number
          /\ y \in Number
          /\ GCD(x, y) = GCD(M, N)

THEOREM PositiveDifference ==
  \A p, q \in Number : p < q => q - p \in Number
PROOF
  BY SMT DEF Number

THEOREM InitImpliesIndInv ==
  Init => IndInv
PROOF
  BY NumberAssumption DEF Init, IndInv

THEOREM StepPreservesIndInv ==
  IndInv /\ [Next]_<<x, y>> => IndInv'
PROOF
  <1>1. ASSUME IndInv, [Next]_<<x, y>>
        PROVE  IndInv'
    <2>1. CASE Next
      <3>1. CASE /\ x < y
                  /\ y' = y - x
                  /\ x' = x
        <4>1. y - x \in Number
          BY <1>1, <3>1, PositiveDifference DEF IndInv
        <4>2. GCD(x', y') = GCD(M, N)
          BY <1>1, <3>1, GCDProperty3 DEF IndInv
        <4>3. QED
          BY <1>1, <3>1, <4>1, <4>2 DEF IndInv
      <3>2. CASE /\ y < x
                  /\ x' = x-y
                  /\ y' = y
        <4>1. x - y \in Number
          BY <1>1, <3>2, PositiveDifference DEF IndInv
        <4>2. GCD(x', y') = GCD(M, N)
          BY <1>1, <3>2, <4>1, GCDProperty2, GCDProperty3 DEF IndInv
        <4>3. QED
          BY <1>1, <3>2, <4>1, <4>2 DEF IndInv
      <3>3. QED
        BY <2>1, <3>1, <3>2 DEF Next
    <2>2. CASE <<x, y>>' = <<x, y>>
      BY <1>1, <2>2, SMT DEF IndInv
    <2>3. QED
      BY <1>1, <2>1, <2>2
  <1>2. QED
    BY <1>1

THEOREM IndInvImpliesResultCorrect ==
  IndInv => ResultCorrect
PROOF
  BY GCDProperty1 DEF IndInv, ResultCorrect

THEOREM Correctness == Spec => []ResultCorrect
PROOF
  <1>1. QED
    BY InitImpliesIndInv, StepPreservesIndInv, IndInvImpliesResultCorrect, PTL DEF Spec
=======================================================
