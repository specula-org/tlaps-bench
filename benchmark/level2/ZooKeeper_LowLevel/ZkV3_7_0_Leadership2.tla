------------------------ MODULE ZkV3_7_0_Leadership2 ------------------------

EXTENDS ZkV3_7_0

Leadership2 == \A epoch \in 1..MAXEPOCH: Cardinality(epochLeader[epoch]) <= 1

THEOREM Spec => []Leadership2
PROOF OBVIOUS

=============================================================================
