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
PROOF
  <1>1. Len(s) \in Nat /\ s \in [1..Len(s) -> S]
    BY LenAxiom
  <1>2. j \in Nat
    BY <1>1 DEF Nat
  <1>3. SubSeq(s, 1, j) = [i \in 1..j |-> s[i]]
    BY SubSeqDef
  <1>4. [i \in 1..j |-> s[i]] \in [1..j -> S]
  PROOF
    <2>1. \A i \in 1..j : i \in 1..Len(s)
      BY <1>1
    <2>2. \A i \in 1..j : s[i] \in S
      BY <1>1, <2>1
    <2> QED
      BY <2>2
  <1>5. [i \in 1..j |-> s[i]] \in Seq(S)
    BY <1>2, <1>4, SeqDef
  <1>6. SubSeq(s, 1, j) \in Seq(S)
    BY <1>3, <1>5
  <1>7. Len(SubSeq(s, 1, j)) = j
  PROOF
    <2>1. DOMAIN [i \in 1..j |-> s[i]] = 1..j
      OBVIOUS
    <2>2. DOMAIN SubSeq(s, 1, j) = 1..j
      BY <1>3, <2>1
    <2> QED
      BY <1>2, <1>6, <2>2, LenDomain
  <1> QED
    BY <1>3, <1>6, <1>7

=============================================================================
