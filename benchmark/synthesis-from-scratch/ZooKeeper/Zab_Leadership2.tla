--------------------------- MODULE Zab_Leadership2 ---------------------------

EXTENDS Zab

Leadership2 == \A epoch \in 1..MAXEPOCH: Cardinality(epochLeader[epoch]) <= 1

THEOREM Spec => []Leadership2
PROOF OBVIOUS

=============================================================================
