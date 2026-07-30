---- MODULE Barriers_AllProcsInRdv ----
EXTENDS Barriers_AllProcsInRdvScaffold
LEMMA AllProcsInRdv == 
    (Cardinality(ProcsInRdv) = N) => (\A p \in ProcSet : rdvsection(p))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
