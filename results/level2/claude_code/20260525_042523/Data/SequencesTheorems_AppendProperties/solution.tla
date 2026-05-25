-------------------------- MODULE SequencesTheorems_AppendProperties -------------------------
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

(***************************************************************************)
(* A sequence in Seq(S) is a function whose domain is the interval         *)
(* 1..Len(seq) and whose values lie in S.  This follows from the axioms    *)
(* SeqDef and LenDef.                                                      *)
(***************************************************************************)
LEMMA SeqAsBox == \A S : \A seq \in Seq(S) : seq \in [1..Len(seq) -> S]
<1> TAKE S
<1> TAKE seq \in Seq(S)
<1>1. seq \in UNION {[1..n -> S] : n \in Nat}
      BY SeqDef
<1>2. PICK n \in Nat : seq \in [1..n -> S]
      BY <1>1
<1>3. /\ Len(seq) \in Nat
      /\ DOMAIN seq = 1..Len(seq)
      BY LenDef
<1>4. DOMAIN seq = 1..n
      BY <1>2
<1>5. 1..n = 1..Len(seq)
      BY <1>3, <1>4
<1>6. n = Len(seq)
      BY <1>5, <1>3, <1>2
<1> QED
      BY <1>2, <1>6

THEOREM AppendProperties ==
          \A S :
            \A seq \in Seq(S), elt \in S :
                /\ Append(seq, elt) \in Seq(S)
                /\ Len(Append(seq, elt)) = Len(seq)+1
                /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
                /\ Append(seq, elt)[Len(seq)+1] = elt
<1> TAKE S
<1> TAKE seq \in Seq(S), elt \in S
<1> DEFINE n == Len(seq)
<1> DEFINE app == [i \in 1..(n+1) |-> IF i = n+1 THEN elt ELSE seq[i]]
<1>n. /\ n \in Nat
      /\ DOMAIN seq = 1..n
      BY LenDef
<1>box. seq \in [1..n -> S]
      BY SeqAsBox
(***************************************************************************)
(* Append(seq, elt) is literally the function [i \in 1..n+1 |-> ...].      *)
(***************************************************************************)
<1>app. Append(seq, elt) = app
      BY <1>n
(***************************************************************************)
(* Step 1: Append(seq, elt) \in Seq(S).                                    *)
(***************************************************************************)
<1>1. Append(seq, elt) \in Seq(S)
      <2>1. \A i \in 1..(n+1) : (IF i = n+1 THEN elt ELSE seq[i]) \in S
            BY <1>box
      <2>2. app \in [1..(n+1) -> S]
            BY <2>1
      <2>3. n+1 \in Nat
            BY <1>n
      <2>4. app \in UNION {[1..m -> S] : m \in Nat}
            BY <2>2, <2>3
      <2>5. app \in Seq(S)
            BY <2>4, SeqDef
      <2> QED
            BY <2>5, <1>app
(***************************************************************************)
(* Step 2: Len(Append(seq, elt)) = Len(seq) + 1.                           *)
(***************************************************************************)
<1>2. Len(Append(seq, elt)) = n+1
      <2>1. /\ Len(Append(seq, elt)) \in Nat
            /\ DOMAIN Append(seq, elt) = 1..Len(Append(seq, elt))
            BY <1>1, LenDef
      <2>2. DOMAIN Append(seq, elt) = 1..(n+1)
            BY <1>app
      <2>3. 1..Len(Append(seq, elt)) = 1..(n+1)
            BY <2>1, <2>2
      <2> QED
            BY <2>3, <2>1, <1>n
(***************************************************************************)
(* Step 3: Append(seq, elt)[i] = seq[i] for i in 1..Len(seq).              *)
(***************************************************************************)
<1>3. \A i \in 1..n : Append(seq, elt)[i] = seq[i]
      <2> TAKE i \in 1..n
      <2>1. i \in 1..(n+1) /\ i # n+1
            BY <1>n
      <2>2. app[i] = seq[i]
            BY <2>1
      <2> QED
            BY <2>2, <1>app
(***************************************************************************)
(* Step 4: Append(seq, elt)[Len(seq)+1] = elt.                             *)
(***************************************************************************)
<1>4. Append(seq, elt)[n+1] = elt
      <2>1. (n+1) \in 1..(n+1)
            BY <1>n
      <2>2. app[n+1] = elt
            BY <2>1
      <2> QED
            BY <2>2, <1>app
<1> QED
      BY <1>1, <1>2, <1>3, <1>4
-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)


-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Head and Tail                                 *)
(***************************************************************************)


=============================================================================
