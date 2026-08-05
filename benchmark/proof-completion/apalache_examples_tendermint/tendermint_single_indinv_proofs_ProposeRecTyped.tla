---- MODULE tendermint_single_indinv_proofs_ProposeRecTyped ----
EXTENDS tendermint_single_indinv_proofs_ProposeRecTypedScaffold
LEMMA ProposeRecTyped ==
  ASSUME NEW s \in (Corr \union Faulty), NEW rr \in (0)..(MaxRound),
         NEW pr \in ((ValidValues \union InvalidValues) \union {-1}),
         NEW vr \in ((0)..(MaxRound) \union {-1})
  PROVE  [proposal |-> pr, round |-> rr, src |-> s, valid_round |-> vr]
           \in {[proposal |-> t[3], round |-> t[2], src |-> t[1], valid_round |-> t[4]]:
                  t \in ((Corr \union Faulty)) \X ((0)..(MaxRound)) \X (((ValidValues \union InvalidValues) \union {-1})) \X (((0)..(MaxRound) \union {-1}))}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
