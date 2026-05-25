--------------------------- MODULE GCD_GCD1 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
(* m is a divisor of itself, since m = m * 1. *)
LEMMA SelfDiv == ASSUME NEW m \in Nat \ {0} PROVE m \in DivisorsOf(m)
PROOF
<1>1. m \in Int OBVIOUS
<1>2. m = m * 1 OBVIOUS
<1>3. Divides(m, m) BY <1>1, <1>2 DEF Divides
<1> QED BY <1>1, <1>3 DEF DivisorsOf

(* For a positive m, every divisor p of m satisfies p <= m. *)
LEMMA DivBound == ASSUME NEW m \in Nat \ {0}, NEW p \in DivisorsOf(m) PROVE m >= p
PROOF
<1>1. p \in Int /\ Divides(p, m) BY DEF DivisorsOf
<1>2. PICK q \in Int : m = p * q BY <1>1 DEF Divides
<1>3. m \in Int /\ m >= 1 OBVIOUS
<1> QED BY <1>1, <1>2, <1>3

(* If mx is an upper bound contained in a set S of integers, SetMax(S) = mx. *)
LEMMA SetMaxEq ==
  ASSUME NEW S, S \subseteq Int, NEW mx, mx \in S, \A j \in S : mx >= j
  PROVE SetMax(S) = mx
PROOF
<1> DEFINE P(i) == i \in S /\ (\A j \in S : i >= j)
<1>1. P(mx) BY DEF P
<1>2. \A x : P(x) => x = mx
  <2>1. TAKE x
  <2>2. ASSUME P(x) PROVE x = mx
    <3>1. x \in Int /\ mx \in Int BY <2>2 DEF P
    <3>2. x >= mx BY <2>2, <1>1 DEF P
    <3>3. mx >= x BY <2>2, <1>1 DEF P
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>2
<1>3. SetMax(S) = (CHOOSE i : P(i)) BY DEF SetMax, P
<1> QED BY <1>1, <1>2, <1>3

THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
PROOF
<1> TAKE m \in Nat \ {0}
<1>1. DivisorsOf(m) \cap DivisorsOf(m) = DivisorsOf(m) OBVIOUS
<1>2. GCD(m, m) = SetMax(DivisorsOf(m)) BY <1>1 DEF GCD
<1>3. DivisorsOf(m) \subseteq Int BY DEF DivisorsOf
<1>4. m \in DivisorsOf(m) BY SelfDiv
<1>5. \A j \in DivisorsOf(m) : m >= j BY DivBound
<1>6. SetMax(DivisorsOf(m)) = m BY <1>3, <1>4, <1>5, SetMaxEq
<1> QED BY <1>2, <1>6
------------------------------------------------------------------
------------------------------------------------------------------
===================================================================