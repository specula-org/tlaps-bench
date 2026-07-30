---- MODULE PaxosCommit_proof_MaxFnRec ----
EXTENDS PaxosCommit_proof_MaxFnRecScaffold
LEMMA MaxFnRec ==
  ASSUME NEW S, IsFiniteSet(S), NEW T \in SUBSET S
  PROVE  MaxFn(S)[T] = MaxDef(MaxFn(S), T)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
