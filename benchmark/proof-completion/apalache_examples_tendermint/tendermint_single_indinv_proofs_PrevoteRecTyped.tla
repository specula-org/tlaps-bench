---- MODULE tendermint_single_indinv_proofs_PrevoteRecTyped ----
EXTENDS tendermint_single_indinv_proofs_PrevoteRecTypedScaffold
LEMMA PrevoteRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW idv \in ((ValidValues \union InvalidValues) \union {-1})
  PROVE  [id |-> idv, kind |-> "PREVOTE_OF_VOTEKIND", round |-> rr, src |-> s]
           \in {[id |-> t[3], kind |-> "PREVOTE_OF_VOTEKIND", round |-> t[2], src |-> t[1]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1}))}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
