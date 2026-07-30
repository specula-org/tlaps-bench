---- MODULE SumSequence_FrontDef ----
EXTENDS SumSequence_FrontDefScaffold
THEOREM FrontDef  ==  \A S : \A s \in Seq(S) :
                        Front(s) = [i \in 1..(Len(s)-1) |-> s[i]]
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
