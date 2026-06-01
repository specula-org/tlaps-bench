-------------------------------- MODULE Sets_FiniteSubset --------------------------------
EXTENDS Integers, NaturalsInduction, TLAPS

FT == INSTANCE FunctionTheorems

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

LEMMA BijectionBridge ==
  \A f, S, T : IsBijection(f, S, T) <=> f \in FT!Bijection(S, T)
PROOF
  BY DEF IsBijection, FT!Bijection, FT!Injection, FT!Surjection,
         FT!IsInjective

LEMMA ExistsBijectionBridge ==
  \A S, T : (\E f : IsBijection(f, S, T)) <=> FT!ExistsBijection(S, T)
PROOF
  BY BijectionBridge DEF FT!ExistsBijection

LEMMA NatBijSubset ==
  ASSUME NEW T, NEW m \in Nat, \E f : IsBijection(f, 1..m, T),
         NEW S, S \subseteq T
  PROVE  \E n \in Nat : (\E g : IsBijection(g, 1..n, S)) /\ n \leq m
PROOF
<1>1. FT!ExistsBijection(1..m, T)
  BY ExistsBijectionBridge
<1>2. S \in SUBSET T
  OBVIOUS
<1>3. \E n \in Nat : FT!ExistsBijection(1..n, S) /\ n \leq m
  BY <1>1, <1>2, FT!Fun_NatBijSubset
<1>. QED
  BY <1>3, ExistsBijectionBridge

------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------

-----------------------------------------------------------------------------

THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
PROOF
<1>1. /\ Cardinality(TT) \in Nat
      /\ \E f : IsBijection(f, 1..Cardinality(TT), TT)
  BY CardinalityAxiom
<1>2. PICK n \in Nat :
        /\ \E g : IsBijection(g, 1..n, S)
        /\ n \leq Cardinality(TT)
  BY <1>1, NatBijSubset
<1>3. IsFiniteSet(S)
  BY <1>2 DEF IsFiniteSet
<1>4. n = Cardinality(S)
  BY <1>2, <1>3, CardinalityAxiom
<1>. QED
  BY <1>2, <1>3, <1>4
-------------------------------------------------------

-----------------------------------------------------------------------------

-------------------------------------------------------

=============================================================================
