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

IndInv == /\ x \in Number
          /\ y \in Number
          /\ GCD(x, y) = GCD(M, N)

LEMMA InitInv == Init => IndInv
  BY NumberAssumption DEF Init, IndInv

LEMMA NextInv == IndInv /\ [Next]_<<x,y>> => IndInv'
  <1> SUFFICES ASSUME IndInv, [Next]_<<x,y>>
               PROVE  IndInv'
    OBVIOUS
  <1>1. x \in Number BY DEF IndInv
  <1>2. y \in Number BY DEF IndInv
  <1>3. GCD(x, y) = GCD(M, N) BY DEF IndInv
  <1>4. CASE Next
    <2>1. CASE x < y /\ y' = y - x /\ x' = x
      <3>1. y - x \in Nat /\ y - x # 0
        BY <1>1, <1>2, <2>1
      <3>2. y - x \in Number
        BY <3>1
      <3>3. GCD(x, y - x) = GCD(x, y)
        BY GCDProperty3, <1>1, <1>2, <2>1
      <3>4. GCD(x', y') = GCD(M, N)
        BY <1>3, <2>1, <3>3
      <3>5. x' \in Number /\ y' \in Number
        BY <1>1, <2>1, <3>2
      <3>6. QED BY <3>4, <3>5 DEF IndInv
    <2>2. CASE y < x /\ x' = x - y /\ y' = y
      <3>1. x - y \in Nat /\ x - y # 0
        BY <1>1, <1>2, <2>2
      <3>2. x - y \in Number
        BY <3>1
      <3>3. GCD(x, y) = GCD(y, x)
        BY GCDProperty2, <1>1, <1>2
      <3>4. GCD(y, x) = GCD(y, x - y)
        BY GCDProperty3, <1>1, <1>2, <2>2
      <3>5. GCD(y, x - y) = GCD(x - y, y)
        BY GCDProperty2, <1>2, <3>2
      <3>6. GCD(x - y, y) = GCD(M, N)
        BY <1>3, <3>3, <3>4, <3>5
      <3>7. GCD(x', y') = GCD(M, N)
        BY <2>2, <3>6
      <3>8. x' \in Number /\ y' \in Number
        BY <1>2, <2>2, <3>2
      <3>9. QED BY <3>7, <3>8 DEF IndInv
    <2>3. QED BY <1>4, <2>1, <2>2 DEF Next
  <1>5. CASE UNCHANGED <<x,y>>
    BY <1>1, <1>2, <1>3, <1>5 DEF IndInv
  <1>6. QED BY <1>4, <1>5

LEMMA InvImpliesCorrect == IndInv => ResultCorrect
  <1> SUFFICES ASSUME IndInv, x = y
               PROVE  x = GCD(M, N)
    BY DEF ResultCorrect
  <1>1. x \in Number BY DEF IndInv
  <1>2. GCD(x, x) = x
    BY GCDProperty1, <1>1
  <1>3. GCD(x, y) = GCD(M, N) BY DEF IndInv
  <1>4. QED BY <1>2, <1>3

THEOREM Correctness == Spec => []ResultCorrect
  <1>1. Init => IndInv BY InitInv
  <1>2. IndInv /\ [Next]_<<x,y>> => IndInv' BY NextInv
  <1>3. IndInv => ResultCorrect BY InvImpliesCorrect
  <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec
=======================================================