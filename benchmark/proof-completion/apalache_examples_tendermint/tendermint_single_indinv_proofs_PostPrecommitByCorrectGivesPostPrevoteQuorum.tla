---- MODULE tendermint_single_indinv_proofs_PostPrecommitByCorrectGivesPostPrevoteQuorum ----
EXTENDS tendermint_single_indinv_proofs_PostPrecommitByCorrectGivesPostPrevoteQuorumScaffold
LEMMA PostPrecommitByCorrectGivesPostPrevoteQuorum ==
  ASSUME TypedIndInv, Step, NEW r \in (0)..(MaxRound),
         NEW m \in msgs_precommit'[r], m.src \in Corr, m.id \in ValidValues
  PROVE  Cardinality(PVSetP(r, m.id)) >= 2 * T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
