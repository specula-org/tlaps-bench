------------------------ MODULE ZkV3_7_0_Leadership2Defs ------------------------

EXTENDS ZkV3_7_0Model

Leadership2 == \A epoch \in 1..MAXEPOCH: Cardinality(epochLeader[epoch]) <= 1

=============================================================================
