---- MODULE Sets_IsBijectionInverse ----
EXTENDS Sets_IsBijectionInverseDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T, 
         IsBijection(f, S, T) 
  PROVE  \E g : IsBijection(g, T, S)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
