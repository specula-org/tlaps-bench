-------------------------- MODULE SequencesTheorems_AppendDef -------------------------

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

-----------------------------------------------------------------------------

THEOREM AppendDef ==
   ASSUME NEW S, NEW seq \in Seq(S), NEW elt
   PROVE  Append(seq, elt) =
                [i \in 1..(Len(seq)+1) |-> IF i \leq Len(seq) THEN seq[i]
                                                              ELSE elt]
PROOF
  BY DEF Append, \o

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
