---- MODULE BPConProof_KnowsSafeAtDef ----
EXTENDS BPConProof_KnowsSafeAtDefScaffold
LEMMA KnowsSafeAtDef ==
        \A a, b, v :
           /\ KnowsSafeAt(a, b, v) <=> KS1(KSet(a,b)) \/ KS2(v, b, KSet(a, b))
           /\ KnowsSafeAt(a, b, v)' <=> KS1(KSet(a,b)') \/ KS2(v, b, KSet(a, b)')
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
