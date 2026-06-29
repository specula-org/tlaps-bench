-------------------------- MODULE SequencesTheorems_ConcatDef -------------------------
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

THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
PROOF OMITTED

THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)
PROOF OMITTED

THEOREM HeadAndTailOfSeq ==
   ASSUME NEW S,
          NEW seq \in Seq(S), seq # << >>
   PROVE  /\ Head(seq) \in S
          /\ Tail(seq) \in Seq(S)
  (*************************************************************************)
  (* Note: the way Tail is defined, Tail(<< >>) \in Seq(S) is actually     *)
  (* valid (because Tail(<< >>) = << >>).                                  *)
  (*************************************************************************)
PROOF OMITTED

Remove(i, seq) == [j \in 1..(Len(seq)-1) |->
                                   IF j < i THEN seq[j] ELSE seq[j+1]]
THEOREM RemoveSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE   Remove(i, seq) \in Seq(S)
PROOF OMITTED

(***************************************************************************)
(*                                    Append                               *)
(***************************************************************************)
THEOREM AppendDef ==
   ASSUME NEW S, NEW seq \in Seq(S), NEW elt
   PROVE  Append(seq, elt) =
                [i \in 1..(Len(seq)+1) |-> IF i \leq Len(seq) THEN seq[i]
                                                              ELSE elt]
PROOF OMITTED

THEOREM AppendProperties ==
          \A S :
            \A seq \in Seq(S), elt \in S :
                /\ Append(seq, elt) \in Seq(S)
                /\ Len(Append(seq, elt)) = Len(seq)+1
                /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
                /\ Append(seq, elt)[Len(seq)+1] = elt
PROOF OMITTED
(***************************************************************************)
(*                           Concatenation (\o)                            *)
(***************************************************************************)
THEOREM ConcatDef ==
           \A S: 
           \A s1, s2 \in Seq(S) : s1 \o s2 =
                         [i \in 1..(Len(s1)+Len(s2)) |->
                           IF i \leq Len(s1) THEN s1[i]
                                             ELSE s2[i-Len(s1)]]
PROOF OBVIOUS

(***************************************************************************)
(*                           Head and Tail                                 *)
(***************************************************************************)

=============================================================================
