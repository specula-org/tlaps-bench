---- MODULE tendermint_single_indinv_proofs_Pres_Bounded_Faulty ----
EXTENDS tendermint_single_indinv_proofs_Pres_Bounded_FaultyScaffold
THEOREM Pres_Bounded_Faulty ==
  ASSUME TypedIndInv, FaultyStep,
         UNCHANGED <<round, step, decision, locked_value, locked_round, valid_value, valid_round, last_action>>
  PROVE  AllValidAndLockedRoundBounded'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
