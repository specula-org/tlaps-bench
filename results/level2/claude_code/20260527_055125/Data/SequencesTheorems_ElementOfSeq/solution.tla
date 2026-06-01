-------------------------- MODULE SequencesTheorems_ElementOfSeq -------------------------

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
THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
PROOF
  <1>1. seq \in UNION {[1..nn -> S] : nn \in Nat}
    BY SeqDef
  <1>2. PICK m \in Nat : seq \in [1..m -> S]
    BY <1>1
  <1>3. DOMAIN seq = 1..m
    BY <1>2
  <1>4. DOMAIN seq = 1..Len(seq)
    BY LenDef
  <1>5. 1..m = 1..Len(seq)
    BY <1>3, <1>4
  <1>6. n \in 1..m
    BY <1>5
  <1>7. seq[n] \in S
    BY <1>2, <1>6
  <1>8. QED BY <1>7

------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
