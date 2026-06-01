-------------------------- MODULE SequencesTheorems_RemoveSeq -------------------------

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

------------------------------------------------------------------
Remove(i, seq) == [j \in 1..(Len(seq)-1) |->
                                   IF j < i THEN seq[j] ELSE seq[j+1]]

LEMMA SeqElem ==
   ASSUME NEW S, NEW seq \in Seq(S), NEW j \in 1..Len(seq)
   PROVE  seq[j] \in S
PROOF
  <1>1. \E n \in Nat : seq \in [1..n -> S]
    BY SeqDef
  <1>2. PICK n \in Nat : seq \in [1..n -> S]
    BY <1>1
  <1>3. DOMAIN seq = 1..n
    BY <1>2
  <1>4. DOMAIN seq = 1..Len(seq)
    BY LenDef
  <1>5. 1..n = 1..Len(seq)
    BY <1>3, <1>4
  <1>6. j \in 1..n
    BY <1>5
  <1> QED
    BY <1>2, <1>6

THEOREM RemoveSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE   Remove(i, seq) \in Seq(S)
PROOF
  <1>1. Len(seq) \in Nat
    BY LenDef
  <1>2. Len(seq) - 1 \in Nat
    BY <1>1
  <1>3. ASSUME NEW j \in 1..(Len(seq)-1)
        PROVE (IF j < i THEN seq[j] ELSE seq[j+1]) \in S
    <2>1. j \in 1..Len(seq)
      BY <1>1
    <2>2. j+1 \in 1..Len(seq)
      BY <1>1
    <2>3. seq[j] \in S
      BY <2>1, SeqElem
    <2>4. seq[j+1] \in S
      BY <2>2, SeqElem
    <2> QED
      BY <2>3, <2>4
  <1>4. Remove(i, seq) \in [1..(Len(seq)-1) -> S]
    BY <1>3 DEF Remove
  <1>5. Remove(i, seq) \in UNION {[1..n -> S] : n \in Nat}
    BY <1>2, <1>4
  <1> QED
    BY <1>5, SeqDef

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
