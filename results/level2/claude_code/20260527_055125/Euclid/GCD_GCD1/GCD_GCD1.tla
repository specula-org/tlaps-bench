--------------------------- MODULE GCD_GCD1 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------

LEMMA MDividesM ==
  ASSUME NEW m \in Nat \ {0}
  PROVE  m \in DivisorsOf(m)
PROOF
  <1>1. m \in Int OBVIOUS
  <1>2. m = m * 1 OBVIOUS
  <1>3. \E q \in Int : m = m * q
    BY <1>2
  <1>4. Divides(m, m) BY <1>3 DEF Divides
  <1>5. QED BY <1>1, <1>4 DEF DivisorsOf

LEMMA DivisorLeq ==
  ASSUME NEW m \in Nat \ {0}, NEW p \in DivisorsOf(m)
  PROVE  p <= m
PROOF
  <1>1. p \in Int BY DEF DivisorsOf
  <1>2. Divides(p, m) BY DEF DivisorsOf
  <1>3. PICK q \in Int : m = p * q BY <1>2 DEF Divides
  <1>4. m \in Int /\ m > 0 OBVIOUS
  <1>5. CASE p <= 0
    BY <1>1, <1>4, <1>5
  <1>6. CASE p > 0
    <2>1. p > 0 BY <1>6
    <2>2. q # 0
      <3>1. ASSUME q = 0 PROVE FALSE
        <4>1. m = p * 0 BY <1>3, <3>1
        <4>2. p * 0 = 0 BY <1>1
        <4>3. m = 0 BY <4>1, <4>2
        <4>4. QED BY <4>3, <1>4
      <3>2. QED BY <3>1
    <2>3. q > 0
      <3>1. ASSUME q < 0 PROVE FALSE
        <4>1. p * q < 0 BY <2>1, <3>1, <1>1
        <4>2. m < 0 BY <1>3, <4>1
        <4>3. QED BY <4>2, <1>4
      <3>2. QED BY <2>2, <3>1
    <2>4. q >= 1 BY <2>3
    <2>5. p * q >= p * 1 BY <2>1, <2>4, <1>1
    <2>6. p * 1 = p BY <1>1
    <2>7. m >= p BY <1>3, <2>5, <2>6
    <2>8. QED BY <2>7, <1>1, <1>4
  <1>7. p <= 0 \/ p > 0 BY <1>1
  <1>8. QED BY <1>5, <1>6, <1>7

THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
PROOF
  <1> SUFFICES ASSUME NEW m \in Nat \ {0}
               PROVE  GCD(m, m) = m
    OBVIOUS
  <1>1. DivisorsOf(m) \cap DivisorsOf(m) = DivisorsOf(m)
    OBVIOUS
  <1>2. GCD(m, m) = SetMax(DivisorsOf(m))
    BY <1>1 DEF GCD
  <1>3. m \in DivisorsOf(m) BY MDividesM
  <1>4. \A j \in DivisorsOf(m) : m >= j
    <2> SUFFICES ASSUME NEW j \in DivisorsOf(m) PROVE m >= j
      OBVIOUS
    <2>1. j <= m BY DivisorLeq
    <2>2. j \in Int BY DEF DivisorsOf
    <2>3. m \in Int OBVIOUS
    <2>4. QED BY <2>1, <2>2, <2>3
  <1>5. \A i \in DivisorsOf(m) : (\A j \in DivisorsOf(m) : i >= j) => i = m
    <2> SUFFICES ASSUME NEW i \in DivisorsOf(m),
                        \A j \in DivisorsOf(m) : i >= j
                 PROVE  i = m
      OBVIOUS
    <2>1. i >= m BY <1>3
    <2>2. m >= i BY <1>4
    <2>3. i \in Int BY DEF DivisorsOf
    <2>4. m \in Int OBVIOUS
    <2>5. QED BY <2>1, <2>2, <2>3, <2>4
  <1>6. SetMax(DivisorsOf(m)) = m
    BY <1>3, <1>4, <1>5 DEF SetMax
  <1>7. QED BY <1>2, <1>6
------------------------------------------------------------------
------------------------------------------------------------------
===================================================================
