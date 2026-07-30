---- MODULE EWD998PCal_proof_BagRemove_tok_preserves_pl ----
EXTENDS EWD998PCal_proof_BagRemove_tok_preserves_plScaffold
USE NAssumption
LEMMA BagRemove_tok_preserves_pl ==
  ASSUME NEW B, NEW t, t.type = "tok"
  PROVE  PlCount(BagRemove(B, t)) = PlCount(B)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
