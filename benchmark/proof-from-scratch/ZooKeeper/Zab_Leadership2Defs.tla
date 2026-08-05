--------------------------- MODULE Zab_Leadership2Defs ---------------------------

EXTENDS ZabModel

Leadership2 == \A epoch \in 1..MAXEPOCH: Cardinality(epochLeader[epoch]) <= 1

=============================================================================
