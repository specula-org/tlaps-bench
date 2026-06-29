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
PROOF OBVIOUS

Remove(i, seq) == [j \in 1..(Len(seq)-1) |->
                                   IF j < i THEN seq[j] ELSE seq[j+1]]

(***************************************************************************)
(*                                    Append                               *)
(***************************************************************************)

(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)

(***************************************************************************)
(*                           Head and Tail                                 *)
(***************************************************************************)

=============================================================================
