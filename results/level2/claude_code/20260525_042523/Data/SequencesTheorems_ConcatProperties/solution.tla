-------------------------- MODULE SequencesTheorems_ConcatProperties -------------------------
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

-----------------------------------------------------------------------------
(***************************************************************************)
(*                                    Append                               *)
(***************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)

(***************************************************************************)
(* A sequence is a function from 1..Len(seq) into its element type.  This   *)
(* combines the membership information in SeqDef with the domain            *)
(* characterization in LenDef.                                             *)
(***************************************************************************)
LEMMA SeqIsFunc ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  seq \in [1..Len(seq) -> S]
PROOF
<1>1. PICK m \in Nat : seq \in [1..m -> S]  BY SeqDef
<1>2. DOMAIN seq = 1..m  BY <1>1
<1>3. DOMAIN seq = 1..Len(seq)  BY LenDef
<1>4. [1..m -> S] = [1..Len(seq) -> S]  BY <1>2, <1>3
<1> QED  BY <1>1, <1>4

(***************************************************************************)
(* Two natural numbers with equal integer intervals 1..a and 1..b are      *)
(* equal.  Used to recover Len from the domain of the concatenation.       *)
(***************************************************************************)
LEMMA IntervalEq ==
  ASSUME NEW a \in Nat, NEW b \in Nat, 1..a = 1..b
  PROVE  a = b
<1>1. SUFFICES ASSUME a # b PROVE FALSE  OBVIOUS
<1>2. CASE a < b
  <2>1. b \in 1..b  BY <1>2
  <2>2. b \notin 1..a  BY <1>2
  <2> QED  BY <2>1, <2>2
<1>3. CASE b < a
  <2>1. a \in 1..a  BY <1>3
  <2>2. a \notin 1..b  BY <1>3
  <2> QED  BY <2>1, <2>2
<1> QED  BY <1>1, <1>2, <1>3

THEOREM ConcatProperties ==
           \A S :
             \A s1, s2 \in Seq(S) :
                 /\ s1 \o s2 \in Seq(S)
                 /\ Len(s1 \o s2) = Len(s1) + Len(s2)
PROOF
<1> TAKE S
<1> TAKE s1, s2 \in Seq(S)
<1> DEFINE n == Len(s1) + Len(s2)
<1> DEFINE body(i) == IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]
<1>n. n \in Nat  BY LenDef
<1>f1. s1 \in [1..Len(s1) -> S]  BY SeqIsFunc
<1>f2. s2 \in [1..Len(s2) -> S]  BY SeqIsFunc
(***********************************************************************)
(* The defining equation of \o; tlapm knows the definition natively.   *)
(***********************************************************************)
<1>cat. s1 \o s2 = [i \in 1..n |-> body(i)]  OBVIOUS
<1>elt. \A i \in 1..n : body(i) \in S
  <2>1. TAKE i \in 1..n
  <2>2. CASE i <= Len(s1)
    <3>1. i \in 1..Len(s1)  BY <2>1, <2>2, LenDef
    <3> QED  BY <3>1, <2>2, <1>f1
  <2>3. CASE ~(i <= Len(s1))
    <3>1. i - Len(s1) \in 1..Len(s2)  BY <2>1, <2>3, LenDef
    <3> QED  BY <3>1, <2>3, <1>f2
  <2> QED  BY <2>2, <2>3
<1>isfun. s1 \o s2 \in [1..n -> S]  BY <1>cat, <1>elt
<1>inseq. s1 \o s2 \in Seq(S)
  <2>1. [1..n -> S] \in {[1..k -> S] : k \in Nat}  BY <1>n
  <2> QED  BY <1>isfun, <2>1, SeqDef
<1>lenpart. Len(s1 \o s2) = Len(s1) + Len(s2)
  <2>1. DOMAIN (s1 \o s2) = 1..n  BY <1>cat
  <2>2. DOMAIN (s1 \o s2) = 1..Len(s1 \o s2)  BY <1>inseq, LenDef
  <2>3. 1..Len(s1 \o s2) = 1..n  BY <2>1, <2>2
  <2>4. Len(s1 \o s2) \in Nat  BY <1>inseq, LenDef
  <2> QED  BY <2>3, <2>4, <1>n, IntervalEq
<1> QED  BY <1>inseq, <1>lenpart

-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Head and Tail                                 *)
(***************************************************************************)


=============================================================================
