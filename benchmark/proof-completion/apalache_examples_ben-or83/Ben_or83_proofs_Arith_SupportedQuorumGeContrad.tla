---- MODULE Ben_or83_proofs_Arith_SupportedQuorumGeContrad ----
EXTENDS Ben_or83_proofs_Arith_SupportedQuorumGeContradScaffold
LEMMA Arith_SupportedQuorumGeContrad ==
  ASSUME NEW rcv \in Nat, NEW dv \in Nat, NEW oth \in Nat,
         rcv >= N - T, rcv <= dv + oth, dv < T + 1, oth < N - 2 * T
  PROVE  FALSE
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
