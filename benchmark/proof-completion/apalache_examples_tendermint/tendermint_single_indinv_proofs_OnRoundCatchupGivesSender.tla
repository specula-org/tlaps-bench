---- MODULE tendermint_single_indinv_proofs_OnRoundCatchupGivesSender ----
EXTENDS tendermint_single_indinv_proofs_OnRoundCatchupGivesSenderScaffold
LEMMA OnRoundCatchupGivesSender ==
  ASSUME IndTypeOk, NEW p \in Corr, OnRoundCatchup(p)
  PROVE  \E rr \in (0)..(MaxRound) :
           /\ round' = [round EXCEPT ![p] = rr]
           /\ rr > round[p]
           /\ \E c \in Corr : c \in AllMsgSenders(rr)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
