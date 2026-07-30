---- MODULE EWD998_proof_PlusACI ----
EXTENDS EWD998_proof_PlusACIScaffold
USE NAssumption
LEMMA PlusACI ==
  /\ IsAssociativeOn(+, Nat)
  /\ IsCommutativeOn(+, Nat)
  /\ IsIdentityOn(+, 0, Nat)
  /\ IsAssociativeOn(+, Int)
  /\ IsCommutativeOn(+, Int)
  /\ IsIdentityOn(+, 0, Int)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
