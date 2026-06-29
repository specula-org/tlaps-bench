------------------------ MODULE BlockingQueue_proofs_DeadlockFreedom ------------------------
EXTENDS BlockingQueue, TLAPS

\* TypeInv will be a conjunct of the inductive invariant, so prove it inductive.
\* An invariant I is inductive, iff Init => I and I /\ [Next]_vars => I. Note
\* though, that TypeInv itself won't imply Invariant though!  TypeInv alone
\* does not help us prove Invariant.
\* Luckily, TLAPS does not require us to decompose the proof into substeps. 
LEMMA TypeCorrect == Spec => []TypeInv
PROOF OMITTED

THEOREM DeadlockFreedom == Spec => []Invariant
PROOF OBVIOUS

=============================================================================
