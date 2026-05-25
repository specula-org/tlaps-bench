-------------------------- MODULE SequencesTheorems_HeadAndTailOfSeq -------------------------
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
LEMMA EmptyFcn == ASSUME NEW T, NEW f \in [{} -> T] PROVE f = << >>
OBVIOUS

THEOREM HeadAndTailOfSeq ==
   ASSUME NEW S,
          NEW seq \in Seq(S), seq # << >>
   PROVE  /\ Head(seq) \in S
          /\ Tail(seq) \in Seq(S)
  (*************************************************************************)
  (* Note: the way Tail is defined, Tail(<< >>) \in Seq(S) is actually     *)
  (* valid (because Tail(<< >>) = << >>).                                  *)
  (*************************************************************************)
PROOF
<1>1. PICK m \in Nat : seq \in [1..m -> S]
  BY SeqDef
<1>2. /\ DOMAIN seq = 1..m
      /\ \A i \in 1..m : seq[i] \in S
  BY <1>1
<1>3. /\ Len(seq) \in Nat
      /\ DOMAIN seq = 1..Len(seq)
  BY LenDef
<1>4. Len(seq) = m
  BY <1>2, <1>3
<1>5. m # 0
  <2>1. SUFFICES ASSUME m = 0 PROVE FALSE
    OBVIOUS
  <2>2. seq \in [{} -> S]
    BY <2>1, <1>1
  <2>3. seq = << >>
    BY <2>2, EmptyFcn
  <2>4. QED
    BY <2>3
<1>6. m \in Nat \ {0}
  BY <1>1, <1>5
<1>7. Head(seq) \in S
  <2>1. Head(seq) = seq[1]
    BY HeadDef
  <2>2. 1 \in 1..m
    BY <1>6
  <2>3. seq[1] \in S
    BY <2>2, <1>2
  <2>4. QED
    BY <2>1, <2>3
<1>8. Tail(seq) \in Seq(S)
  <2>1. Tail(seq) = [i \in 1..(m-1) |-> seq[i+1]]
    BY TailDef, <1>4
  <2>2. m-1 \in Nat
    BY <1>6
  <2>3. \A i \in 1..(m-1) : seq[i+1] \in S
    <3>1. TAKE i \in 1..(m-1)
    <3>2. i+1 \in 1..m
      BY <1>6
    <3>3. QED
      BY <3>2, <1>2
  <2>4. Tail(seq) \in [1..(m-1) -> S]
    BY <2>1, <2>3
  <2>5. QED
    BY <2>2, <2>4, SeqDef
<1>9. QED
  BY <1>7, <1>8

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
