---- MODULE Paxos_NoneNotAValue ----
EXTENDS Paxos_NoneNotAValueScaffold
LEMMA NoneNotAValue == None \notin Values
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
