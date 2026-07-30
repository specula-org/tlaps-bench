---- MODULE Barriers_AllProcsNotInRdv ----
EXTENDS Barriers_AllProcsNotInRdvScaffold
LEMMA AllProcsNotInRdv ==
    (Cardinality(ProcsInRdv) = 0) => ~(\E p \in ProcSet : rdvsection(p))
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
