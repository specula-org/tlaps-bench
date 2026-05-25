-------------------------- MODULE SequencesTheorems_InitialSubSeq -------------------------
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

THEOREM InitialSubSeq ==
   ASSUME NEW S,
          NEW s \in Seq(S),
          NEW j \in 0..Len(s)
   PROVE  /\ SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
          /\ SubSeq(s, 1, j) \in Seq(S)
          /\ Len(SubSeq(s, 1, j)) = j
<1>a. Len(s) \in Nat /\ DOMAIN s = 1..Len(s)
  BY LenDef
<1>b. j \in Nat
  BY <1>a
<1>c. \A i \in 1..Len(s) : s[i] \in S
  <2>1. s \in UNION {[1..n -> S] : n \in Nat}
    BY SeqDef
  <2>2. PICK n \in Nat : s \in [1..n -> S]
    BY <2>1
  <2>3. 1..Len(s) = 1..n
    BY <2>2, <1>a
  <2> QED
    BY <2>2, <2>3
<1>1. SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
  <2>1. SubSeq(s, 1, j) = [i \in 1..(1+j-1) |-> s[i+1-1]]
    BY SubSeqDef
  <2>2. [i \in 1..(1+j-1) |-> s[i+1-1]] = [i \in 1..j |-> s[i]]
    BY <1>b
  <2> QED
    BY <2>1, <2>2
<1>2. SubSeq(s, 1, j) \in Seq(S)
  <2>1. \A i \in 1..j : s[i] \in S
    BY <1>c, <1>a
  <2>2. [i \in 1..j |-> s[i]] \in [1..j -> S]
    BY <2>1
  <2>3. [1..j -> S] \in {[1..n -> S] : n \in Nat}
    BY <1>b
  <2>4. [i \in 1..j |-> s[i]] \in Seq(S)
    BY <2>2, <2>3, SeqDef
  <2> QED
    BY <2>4, <1>1
<1>3. Len(SubSeq(s, 1, j)) = j
  <2>1. DOMAIN SubSeq(s, 1, j) = 1..j
    BY <1>1
  <2>2. /\ DOMAIN SubSeq(s, 1, j) = 1..Len(SubSeq(s, 1, j))
        /\ Len(SubSeq(s, 1, j)) \in Nat
    BY <1>2, LenDef
  <2>3. 1..j = 1..Len(SubSeq(s, 1, j))
    BY <2>1, <2>2
  <2> QED
    BY <2>3, <1>b, <2>2
<1> QED
  BY <1>1, <1>2, <1>3

------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------

------------------------------------------------------------------
Remove(i, seq) == [j \in 1..(Len(seq)-1) |->
                                   IF j < i THEN seq[j] ELSE seq[j+1]]

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
