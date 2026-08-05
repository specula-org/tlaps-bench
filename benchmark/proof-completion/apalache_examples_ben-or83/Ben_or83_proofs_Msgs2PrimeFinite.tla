---- MODULE Ben_or83_proofs_Msgs2PrimeFinite ----
EXTENDS Ben_or83_proofs_Msgs2PrimeFiniteScaffold
THEOREM Msgs2PrimeFinite ==
  ASSUME TypeOK', NEW r \in ROUNDS
  PROVE  IsFiniteSet(msgs2'[r])
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
