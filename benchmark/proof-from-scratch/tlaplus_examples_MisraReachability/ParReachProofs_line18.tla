---- MODULE ParReachProofs_line18 ----
EXTENDS ParReachProofs_line18Defs
\* BEGIN AGENT HELPERS
\* END AGENT HELPERS
THEOREM Spec => R!Init /\ [][R!Next]_R!vars
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
