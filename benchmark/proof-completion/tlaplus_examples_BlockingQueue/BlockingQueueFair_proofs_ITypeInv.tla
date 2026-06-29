---------------------- MODULE BlockingQueueFair_proofs_ITypeInv ----------------------
EXTENDS BlockingQueueFair, SequenceTheorems, TLAPS

(* Prove TypeInv inductive. *)
THEOREM ITypeInv == Spec => []TypeInv
PROOF OBVIOUS

\* BY Z3 DEF Range, IsInjective \* Proof goes through with Tail
                                \* re-defined with the CASE
                                \* statement omitted, which is
                                \* equivalent here due to
                                \* 'ws # <<>>' assumption.

(* Prove BlockingQueueFair implements BlockingQueueSplit *)

=============================================================================
