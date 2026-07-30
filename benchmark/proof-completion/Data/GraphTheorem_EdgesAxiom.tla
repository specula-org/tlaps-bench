---- MODULE GraphTheorem_EdgesAxiom ----
EXTENDS GraphTheorem_EdgesAxiomScaffold
THEOREM EdgesAxiom == \A Nodes :
                       /\ \A m, n \in Nodes : {m, n} \in Edges(Nodes)
                       /\ \A e \in Edges(Nodes) :
                            \E m, n \in Nodes : e = {m, n}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
