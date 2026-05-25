-------------------------- MODULE SequencesTheorems_AppendDef -------------------------
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
THEOREM AppendDef ==
   ASSUME NEW S, NEW seq \in Seq(S), NEW elt
   PROVE  Append(seq, elt) =
                [i \in 1..(Len(seq)+1) |-> IF i \leq Len(seq) THEN seq[i]
                                                              ELSE elt]
PROOF
  (*************************************************************************)
  (* elt need not belong to S, so we move to T = S \cup {elt}, where the   *)
  (* standard reasoning about Append applies, then conclude by function    *)
  (* extensionality.                                                       *)
  (*************************************************************************)
  <1> DEFINE T == S \cup {elt}
  <1> DEFINE n == Len(seq)
  <1> DEFINE rhs == [i \in 1..(n+1) |-> IF i \leq n THEN seq[i] ELSE elt]
  <1>n. n \in Nat
    BY LenDef
  <1>elt. elt \in T
    OBVIOUS
  <1>seqT. seq \in Seq(T)
    BY SeqDef
  (* Properties of Append over the enlarged alphabet T. *)
  <1>1. /\ Append(seq, elt) \in Seq(T)
        /\ Len(Append(seq, elt)) = n + 1
        /\ \A i \in 1 .. n : Append(seq, elt)[i] = seq[i]
        /\ Append(seq, elt)[n + 1] = elt
    BY <1>seqT, <1>elt
  (* Domains coincide. *)
  <1>2. DOMAIN Append(seq, elt) = 1 .. n + 1
    BY <1>1, LenDef
  <1>3. DOMAIN rhs = 1 .. n + 1
    OBVIOUS
  (* Both sides agree pointwise on the common domain 1 .. n+1. *)
  <1>4. \A i \in 1 .. n + 1 : Append(seq, elt)[i] = rhs[i]
    <2> SUFFICES ASSUME NEW i \in 1 .. n + 1
                 PROVE  Append(seq, elt)[i] = rhs[i]
      OBVIOUS
    <2>r. rhs[i] = IF i \leq n THEN seq[i] ELSE elt
      OBVIOUS
    <2>1. CASE i \leq n
      <3>1. i \in 1 .. n
        BY <2>1, <1>n
      <3>2. Append(seq, elt)[i] = seq[i]
        BY <1>1, <3>1
      <3> QED
        BY <3>2, <2>r, <2>1
    <2>2. CASE ~(i \leq n)
      <3>1. i = n + 1
        BY <2>2, <1>n
      <3>2. Append(seq, elt)[i] = elt
        BY <1>1, <3>1
      <3> QED
        BY <3>2, <2>r, <2>2, <3>1
    <2> QED
      BY <2>1, <2>2
  (* Conclude by function extensionality. *)
  <1>5. Append(seq, elt) = rhs
    BY <1>1, <1>2, <1>3, <1>4
  <1> QED
    BY <1>5

-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)


-----------------------------------------------------------------------------
(***************************************************************************)
(*                           Head and Tail                                 *)
(***************************************************************************)


=============================================================================
