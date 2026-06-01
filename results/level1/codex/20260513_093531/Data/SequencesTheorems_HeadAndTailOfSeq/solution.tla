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

THEOREM LenAxiom == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ seq \in [1..Len(seq) -> S]
  PROOF OMITTED

THEOREM LenDomain == \A S :
                       \A s \in Seq(S) :
                         \A n \in Nat : DOMAIN s = 1..n => n = Len(s)
  PROOF OMITTED

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
  PROOF OMITTED

------------------------------------------------------------------
THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
  PROOF OMITTED

------------------------------------------------------------------
THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)
  PROOF OMITTED

------------------------------------------------------------------
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
<1>1. Len(seq) \in Nat
  BY LenAxiom
<1>2. Len(seq) # 0
  BY <1>1, EmptySeq
<1>3. 1 \in 1..Len(seq)
  BY <1>1, <1>2
<1>4. Head(seq) \in S
  BY <1>3, ElementOfSeq DEF HeadDef
<1>5. Len(seq) - 1 \in Nat
  BY <1>1, <1>2
<1>6. \A i \in 1..(Len(seq)-1) : seq[i+1] \in S
  BY <1>1, <1>5, ElementOfSeq
<1>7. [i \in 1..(Len(seq)-1) |-> seq[i+1]] \in [1..(Len(seq)-1) -> S]
  BY <1>6
<1>8. Tail(seq) \in Seq(S)
  BY <1>5, <1>7 DEF TailDef, SeqDef
<1>9. QED
  BY <1>4, <1>8

=============================================================================
