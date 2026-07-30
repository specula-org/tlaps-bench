---- MODULE AllocatorImplementation_proof_PermsRecNonempty ----
EXTENDS AllocatorImplementation_proof_PermsRecNonemptyScaffold
LEMMA PermsRecNonempty ==
  ASSUME NEW g, NEW ss, ss # {}
  PROVE  PermsRec(g, ss) =
           UNION { { Append(sq, x) : sq \in g[ss \ {x}] } : x \in ss }
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
