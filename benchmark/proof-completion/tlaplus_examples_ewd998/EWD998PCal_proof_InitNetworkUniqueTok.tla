---- MODULE EWD998PCal_proof_InitNetworkUniqueTok ----
EXTENDS EWD998PCal_proof_InitNetworkUniqueTokScaffold
USE NAssumption
LEMMA InitNetworkUniqueTok ==
  ASSUME network = [n \in Node |->
                       IF n = Initiator
                       THEN SetToBag({InitTok})
                       ELSE EmptyBag]
  PROVE  /\ DOMAIN network[Initiator] = {InitTok}
         /\ network[Initiator][InitTok] = 1
         /\ \A n \in Node \ {Initiator} : DOMAIN network[n] = {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
