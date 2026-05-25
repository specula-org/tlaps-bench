-------------------------- MODULE SequencesTheorems_RemoveSeq -------------------------
(***************************************************************************)
(* The proofs in this module were essentially written before TLAPS's SMT   *)
(* backend prover was implemented. That backend usually allows for much    *)
(* shorter proofs.                                                         *)
(***************************************************************************)
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
THEOREM RemoveSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE   Remove(i, seq) \in Seq(S)
<1>1. Len(seq) \in Nat /\ DOMAIN seq = 1..Len(seq)
  BY LenDef
<1>2. seq \in [1..Len(seq) -> S]
  <2>1. PICK n \in Nat : seq \in [1..n -> S]
    BY SeqDef
  <2>2. 1..n = 1..Len(seq)
    BY <2>1, <1>1
  <2>3. QED
    BY <2>1, <2>2
<1>3. Len(seq) - 1 \in Nat
  BY <1>1
<1>4. Remove(i, seq) \in [1..(Len(seq)-1) -> S]
  <2> SUFFICES ASSUME NEW j \in 1..(Len(seq)-1)
               PROVE  (IF j < i THEN seq[j] ELSE seq[j+1]) \in S
    BY DEF Remove
  <2>1. CASE j < i
    <3>1. j \in 1..Len(seq)
      BY <1>1, <1>3
    <3>2. seq[j] \in S
      BY <3>1, <1>2
    <3>3. QED
      BY <2>1, <3>2
  <2>2. CASE ~(j < i)
    <3>1. j+1 \in 1..Len(seq)
      BY <1>1, <1>3
    <3>2. seq[j+1] \in S
      BY <3>1, <1>2
    <3>3. QED
      BY <2>2, <3>2
  <2>3. QED
    BY <2>1, <2>2
<1>5. QED
  <2>1. Remove(i, seq) \in UNION {[1..n -> S] : n \in Nat}
    BY <1>3, <1>4
  <2>2. QED
    BY <2>1, SeqDef

-----------------------------------------------------------------------------
(***************************************************************************)
(*                                    Append                               *)
(***************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)


-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Head and Tail                                 *)
(***************************************************************************)


=============================================================================
