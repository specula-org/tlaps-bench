--------------------------- MODULE GCD_GCD3 ---------------------------
EXTENDS Integers
------------------------------------------------------------------
Divides(p, n) == \E q \in Int : n = p * q
DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
-----------------------------------------------------------------------------
THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
  PROOF OMITTED

------------------------------------------------------------------
THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
  PROOF OMITTED

------------------------------------------------------------------
THEOREM GCD3 == \A m, n \in Nat \ {0} : 
                    (n > m) => (GCD(m, n) = GCD(m, n-m))
PROOF
  <1>1. ASSUME NEW m \in Nat \ {0}, NEW n \in Nat \ {0}, n > m
        PROVE  GCD(m, n) = GCD(m, n-m)
    <2>1. DivisorsOf(m) \cap DivisorsOf(n)
          = DivisorsOf(m) \cap DivisorsOf(n-m)
      PROOF
        <3>1. DivisorsOf(m) \cap DivisorsOf(n)
              \subseteq DivisorsOf(m) \cap DivisorsOf(n-m)
          PROOF
            <4>1. ASSUME NEW p \in DivisorsOf(m) \cap DivisorsOf(n)
                  PROVE  p \in DivisorsOf(m) \cap DivisorsOf(n-m)
              <5>1. p \in DivisorsOf(m) /\ p \in DivisorsOf(n) BY <4>1
              <5>2. p \in Int /\ Divides(p, m) /\ Divides(p, n)
                BY <5>1 DEF DivisorsOf
              <5>3. PICK qm \in Int : m = p * qm
                BY <5>2 DEF Divides
              <5>4. PICK qn \in Int : n = p * qn
                BY <5>2 DEF Divides
              <5>5. (p \in Int /\ qn \in Int /\ qm \in Int)
                     => (p * qn - p * qm = p * (qn - qm))
                OBVIOUS (*{ by (isabelle "(auto simp: int_diff_def distrib_left_int minus_mult_right_int add_assoc_int)") }*)
              <5>6. p * qn - p * qm = p * (qn - qm)
                BY <5>2, <5>3, <5>4, <5>5
              <5>7. n - m = p * qn - p * qm BY <5>3, <5>4
              <5>8. n - m = p * (qn - qm) BY <5>6, <5>7
              <5>9. qn - qm \in Int BY <5>3, <5>4
              <5>10. \E q \in Int : n-m = p * q BY <5>8, <5>9
              <5>11. Divides(p, n-m) BY <5>10 DEF Divides
              <5>12. QED BY <5>1, <5>2, <5>11 DEF DivisorsOf
            <4>2. QED BY <4>1
        <3>2. DivisorsOf(m) \cap DivisorsOf(n-m)
              \subseteq DivisorsOf(m) \cap DivisorsOf(n)
          PROOF
            <4>1. ASSUME NEW p \in DivisorsOf(m) \cap DivisorsOf(n-m)
                  PROVE  p \in DivisorsOf(m) \cap DivisorsOf(n)
              <5>1. p \in DivisorsOf(m) /\ p \in DivisorsOf(n-m) BY <4>1
              <5>2. p \in Int /\ Divides(p, m) /\ Divides(p, n-m)
                BY <5>1 DEF DivisorsOf
              <5>3. PICK qm \in Int : m = p * qm
                BY <5>2 DEF Divides
              <5>4. PICK qd \in Int : n - m = p * qd
                BY <5>2 DEF Divides
              <5>5. (p \in Int /\ qm \in Int /\ qd \in Int)
                     => (p * qm + p * qd = p * (qm + qd))
                OBVIOUS (*{ by (isabelle "(auto simp: distrib_left_int)") }*)
              <5>6. p * qm + p * qd = p * (qm + qd)
                BY <5>2, <5>3, <5>4, <5>5
              <5>7. n = p * qm + p * qd BY <5>3, <5>4
              <5>8. n = p * (qm + qd) BY <5>6, <5>7
              <5>9. qm + qd \in Int BY <5>3, <5>4
              <5>10. \E q \in Int : n = p * q BY <5>8, <5>9
              <5>11. Divides(p, n) BY <5>10 DEF Divides
              <5>12. QED BY <5>1, <5>2, <5>11 DEF DivisorsOf
            <4>2. QED BY <4>1
        <3>3. QED BY <3>1, <3>2
    <2>2. QED BY <2>1 DEF GCD
  <1>2. QED BY <1>1

===================================================================
