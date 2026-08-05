---- MODULE tendermint_single_indinv_proofs_PrecommitByCorrectGivesPrevoteQuorum ----
EXTENDS tendermint_single_indinv_proofs_PrecommitByCorrectGivesPrevoteQuorumScaffold
LEMMA PrecommitByCorrectGivesPrevoteQuorum ==
  ASSUME TypedIndInv, NEW r \in (0)..(MaxRound),
         NEW m \in msgs_precommit[r], m.src \in Corr, m.id \in ValidValues
  PROVE  Cardinality(PVSet(r, m.id)) >= 2 * T + 1
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
