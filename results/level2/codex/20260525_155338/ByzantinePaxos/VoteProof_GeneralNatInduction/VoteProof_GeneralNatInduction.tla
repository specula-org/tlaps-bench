----------------------------- MODULE VoteProof_GeneralNatInduction ------------------------------

EXTENDS Integers , FiniteSets, TLC, TLAPS

-----------------------------------------------------------------------------
CONSTANT Value,     
         Acceptor,  
         Quorum     

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  
 
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

VARIABLES votes, maxBal

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

NatPrefix(f, n) == \A j \in 0..n : f[j]

LEMMA NatPrefixBase == \A f : f[0] => NatPrefix(f, 0)
PROOF BY DEF NatPrefix, Isa

LEMMA NatPrefixStep ==
  \A f :
    \A n \in Nat :
      /\ NatPrefix(f, n)
      /\ \A k \in Nat : NatPrefix(f, k) => f[k+1]
      => NatPrefix(f, n+1)
PROOF BY DEF NatPrefix, Isa

THEOREM GeneralNatInduction == 
         \A f : /\ f[0]
                /\ \A n \in Nat : (\A j \in 0..n : f[j]) => f[n+1]
                => \A n \in Nat : f[n]
<1>. SUFFICES ASSUME NEW f,
                     f[0],
                     \A n \in Nat : NatPrefix(f, n) => f[n+1]
              PROVE  \A n \in Nat : f[n]
  BY DEF NatPrefix
<1>. DEFINE g[n \in Nat] == NatPrefix(f, n)
<1>1. g[0]
  BY NatPrefixBase DEF g
<1>2. \A n \in Nat : g[n] => g[n+1]
  <2>. SUFFICES ASSUME NEW n \in Nat, g[n]
                PROVE  g[n+1]
    OBVIOUS
  <2>1. NatPrefix(f, n)
    BY DEF g
  <2>1a. \A k \in Nat : NatPrefix(f, k) => f[k+1]
    OBVIOUS
  <2>2. NatPrefix(f, n+1)
    BY <2>1, <2>1a, NatPrefixStep
  <2>3. n+1 \in Nat
    BY Isa
  <2>. QED
    BY <2>2, <2>3 DEF g
<1>3. \A n \in Nat : g[n]
  BY <1>1, <1>2, SimpleNatInduction
<1>. QED
  BY <1>3 DEF g, NatPrefix
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

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
