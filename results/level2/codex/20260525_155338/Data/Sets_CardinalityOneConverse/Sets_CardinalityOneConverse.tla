-------------------------------- MODULE Sets_CardinalityOneConverse --------------------------------
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

------------------------------------------------------------------

------------------------------------------------------------------

THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
PROOF
<1>1. \E f : IsBijection(f, 1..1, S)
  BY CardinalityAxiom, SimpleArithmetic
<1>2. PICK f : IsBijection(f, 1..1, S)
  BY <1>1
<1>3. 1 \in 1..1
  BY SimpleArithmetic
<1>4. f[1] \in S
  BY <1>2, <1>3 DEF IsBijection
<1>5. S = {f[1]}
  <2>1. \A y : y \in S => y \in {f[1]}
    <3>1. SUFFICES ASSUME NEW y, y \in S
            PROVE  y \in {f[1]}
      OBVIOUS
    <3>2. PICK x \in 1..1 : f[x] = y
      BY <1>2, <3>1 DEF IsBijection
    <3>3. x = 1
      BY <3>2, SimpleArithmetic
    <3>4. y = f[1]
      BY <3>2, <3>3
    <3>. QED BY <3>4
  <2>2. \A y : y \in {f[1]} => y \in S
    BY <1>4
  <2>3. \A y : y \in S <=> y \in {f[1]}
    BY <2>1, <2>2
  <2>. QED BY <2>3, SetExtensionality
<1>. QED BY <1>5

-----------------------------------------------------------------------------

-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
