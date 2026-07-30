---------------------- MODULE BlockingQueueFair_proofs_EmptySeqRangeScaffold ----------------------
EXTENDS BlockingQueueFair, SequenceTheorems, TLAPS

(* Prove TypeInv inductive. *)
THEOREM ITypeInv == Spec => []TypeInv
PROOF OMITTED

=============================================================================
