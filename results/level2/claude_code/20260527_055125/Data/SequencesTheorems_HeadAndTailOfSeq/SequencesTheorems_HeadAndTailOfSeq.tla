-------------------------- MODULE SequencesTheorems_HeadAndTailOfSeq -------------------------

EXTENDS Integers, Sequences, TLAPS

AXIOM SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}

AXIOM LenDef == \A S : \A seq \in Seq(S) :
                     /\ Len(seq) \in Nat 
                     /\ DOMAIN seq = 1..Len(seq)

AXIOM HeadDef == \A s : Head(s) = s[1]
AXIOM TailDef == \A s : Tail(s) = [i \in 1..(Len(s)-1) |-> s[i+1]]

AXIOM SubSeqDef ==
        \A s, m, n : SubSeq(s, m, n) = [i \in 1..(1+n-m) |-> s[i+m-1]]

------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------
THEOREM HeadAndTailOfSeq ==
   ASSUME NEW S,
          NEW seq \in Seq(S), seq # << >>
   PROVE  /\ Head(seq) \in S
          /\ Tail(seq) \in Seq(S)
PROOF
<1>1. seq \in UNION {[1..n -> S] : n \in Nat}
  BY SeqDef
<1>2. PICK k \in Nat : seq \in [1..k -> S]
  BY <1>1
<1>3. Len(seq) \in Nat /\ DOMAIN seq = 1..Len(seq)
  BY LenDef
<1>4. DOMAIN seq = 1..k
  BY <1>2
<1>5. Len(seq) \in Nat \ {0}
  BY <1>2, <1>3, <1>4
<1>6. Len(seq) - 1 \in Nat
  BY <1>5
<1>7. 1 \in DOMAIN seq
  BY <1>3, <1>5
<1>8. Head(seq) \in S
  <2>1. Head(seq) = seq[1]
    BY HeadDef
  <2>2. seq[1] \in S
    BY <1>2, <1>3, <1>4, <1>5, <1>7
  <2>3. QED BY <2>1, <2>2
<1>9. Tail(seq) \in Seq(S)
  <2>1. Tail(seq) = [i \in 1..(Len(seq)-1) |-> seq[i+1]]
    BY TailDef
  <2>2. ASSUME NEW i \in 1..(Len(seq)-1)
        PROVE  seq[i+1] \in S
    <3>1. i+1 \in 1..Len(seq)
      BY <1>3, <1>5, <1>6
    <3>2. i+1 \in DOMAIN seq
      BY <1>3, <3>1
    <3>3. QED BY <1>2, <1>4, <3>1, <3>2
  <2>3. [i \in 1..(Len(seq)-1) |-> seq[i+1]] \in [1..(Len(seq)-1) -> S]
    BY <2>2
  <2>4. Tail(seq) \in [1..(Len(seq)-1) -> S]
    BY <2>1, <2>3
  <2>5. Tail(seq) \in UNION {[1..n -> S] : n \in Nat}
    BY <2>4, <1>6
  <2>6. QED BY <2>5, SeqDef
<1>10. QED BY <1>8, <1>9

------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
