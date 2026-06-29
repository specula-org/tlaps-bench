---------------------- MODULE BlockingQueueFair_proofs_EmptySeqRange ----------------------
EXTENDS BlockingQueueFair, SequenceTheorems, TLAPS

(* Prove TypeInv inductive. *)
THEOREM ITypeInv == Spec => []TypeInv
PROOF OMITTED

LEMMA EmptySeqRange == ASSUME NEW S, NEW seq \in Seq(S)
                       PROVE seq = <<>> <=> Range(seq) = {}
PROOF OBVIOUS

\* BY Z3 DEF Range, IsInjective \* Proof goes through with Tail
                                \* re-defined with the CASE
                                \* statement omitted, which is
                                \* equivalent here due to
                                \* 'ws # <<>>' assumption.

(* Prove BlockingQueueFair implements BlockingQueueSplit *)

=============================================================================
