-------------------------- MODULE SequencesTheorems_InitialSubSeq -------------------------

EXTENDS Integers, Sequences, TLAPS

AXIOM SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}

AXIOM LenDef == \A S : \A seq \in Seq(S) :
                     /\ Len(seq) \in Nat 
                     /\ DOMAIN seq = 1..Len(seq)

AXIOM HeadDef == \A s : Head(s) = s[1]
AXIOM TailDef == \A s : Tail(s) = [i \in 1..(Len(s)-1) |-> s[i+1]]

AXIOM SubSeqDef ==
        \A s, m, n : SubSeq(s, m, n) = [i \in 1..(1+n-m) |-> s[i+m-1]]

LEMMA LenInNat ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  Len(s) \in Nat
BY LenDef

LEMMA SeqElemInRange ==
  ASSUME NEW S, NEW s \in Seq(S), NEW i \in 1..Len(s)
  PROVE  s[i] \in S
<1>1. PICK n \in Nat : s \in [1..n -> S]
  BY SeqDef
<1>2. DOMAIN s = 1..n
  BY <1>1
<1>3. DOMAIN s = 1..Len(s)
  BY LenDef
<1>4. 1..n = 1..Len(s)
  BY <1>2, <1>3
<1>5. i \in 1..n
  BY <1>4
<1>6. QED
  BY <1>1, <1>5

LEMMA OneDotDotEq ==
  ASSUME NEW a \in Nat, NEW b \in Nat, 1..a = 1..b
  PROVE  a = b
<1>1. CASE a = 0
  <2>1. 1..a = {}
    BY <1>1
  <2>2. 1..b = {}
    BY <2>1
  <2>3. b = 0
    BY <2>2
  <2>4. QED
    BY <1>1, <2>3
<1>2. CASE a >= 1
  <2>1. a \in 1..a
    BY <1>2
  <2>2. a \in 1..b
    BY <2>1
  <2>3. a <= b
    BY <2>2
  <2>4. b \in 1..b
    BY <2>3, <1>2
  <2>5. b \in 1..a
    BY <2>4
  <2>6. b <= a
    BY <2>5
  <2>7. QED
    BY <2>3, <2>6
<1>3. QED
  BY <1>1, <1>2

LEMMA FuncInSeq ==
  ASSUME NEW S, NEW n \in Nat, NEW f \in [1..n -> S]
  PROVE  /\ f \in Seq(S)
         /\ Len(f) = n
<1>1. f \in Seq(S)
  BY SeqDef
<1>2. Len(f) \in Nat
  BY <1>1, LenDef
<1>3. DOMAIN f = 1..Len(f)
  BY <1>1, LenDef
<1>4. DOMAIN f = 1..n
  OBVIOUS
<1>5. 1..Len(f) = 1..n
  BY <1>3, <1>4
<1>6. Len(f) = n
  BY <1>2, <1>5, OneDotDotEq
<1>7. QED
  BY <1>1, <1>6

THEOREM InitialSubSeq ==
   ASSUME NEW S,
          NEW s \in Seq(S),
          NEW j \in 0..Len(s)
   PROVE  /\ SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
          /\ SubSeq(s, 1, j) \in Seq(S)
          /\ Len(SubSeq(s, 1, j)) = j
<1>1. Len(s) \in Nat
  BY LenInNat
<1>2. j \in Nat
  BY <1>1
<1>3. SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
  <2>1. SubSeq(s, 1, j) = [i \in 1..(1+j-1) |-> s[i+1-1]]
    BY SubSeqDef
  <2>2. 1+j-1 = j
    BY <1>2
  <2>3. \A i \in 1..j : i+1-1 = i
    BY <1>2
  <2>4. [i \in 1..(1+j-1) |-> s[i+1-1]] = [i \in 1..j |-> s[i]]
    BY <2>2, <2>3
  <2>5. QED
    BY <2>1, <2>4
<1>4. \A i \in 1..j : s[i] \in S
  <2>1. TAKE i \in 1..j
  <2>2. i \in 1..Len(s)
    BY <1>1, <1>2
  <2>3. QED
    BY <2>2, SeqElemInRange
<1>5. [i \in 1..j |-> s[i]] \in [1..j -> S]
  BY <1>4
<1>6. SubSeq(s, 1, j) \in [1..j -> S]
  BY <1>3, <1>5
<1>7. SubSeq(s, 1, j) \in Seq(S) /\ Len(SubSeq(s, 1, j)) = j
  BY <1>2, <1>6, FuncInSeq
<1>8. QED
  BY <1>3, <1>7

------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
