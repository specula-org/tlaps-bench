---- MODULE Sets_IsBijectionTransitive ----
EXTENDS Sets_IsBijectionTransitiveDefs

\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM IsBijectionTransitive ==
  ASSUME NEW f1, NEW f2, NEW S, NEW T, NEW U, 
           IsBijection(f1, S, U),
           IsBijection(f2, U, T) 
  PROVE  \E g : IsBijection(g, S, T)
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
