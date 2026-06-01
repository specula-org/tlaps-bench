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

LEMMA RemoveIsFunction ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE  Remove(i, seq) \in [1..(Len(seq)-1) -> S]
PROOF
<1>1. /\ Len(seq) \in Nat
      /\ DOMAIN seq = 1..Len(seq)
  BY LenDef
<1>2. Len(seq) - 1 \in Nat
  BY <1>1
<1>3. seq \in [1..Len(seq) -> S]
  BY <1>1, SeqDef
<1>4. \A j \in 1..(Len(seq)-1) :
        (IF j < i THEN seq[j] ELSE seq[j+1]) \in S
  <2> SUFFICES ASSUME NEW j \in 1..(Len(seq)-1)
                PROVE  (IF j < i THEN seq[j] ELSE seq[j+1]) \in S
    OBVIOUS
  <2>1. /\ j \in 1..Len(seq)
        /\ j+1 \in 1..Len(seq)
    BY <1>1
  <2>2. /\ seq[j] \in S
        /\ seq[j+1] \in S
    BY <1>3, <2>1
  <2> QED BY <2>2
<1> QED BY <1>4 DEF Remove

THEOREM RemoveSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE   Remove(i, seq) \in Seq(S)
PROOF
<1>1. Remove(i, seq) \in [1..(Len(seq)-1) -> S]
  BY RemoveIsFunction
<1>2. Len(seq) - 1 \in Nat
  BY LenDef
<1>3. Remove(i, seq) \in UNION {[1..n -> S] : n \in Nat}
  BY <1>1, <1>2
<1> QED BY <1>3, SeqDef

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
