

-------------------------- MODULE OpenAddressing_ConsistentDefs --------------------------
EXTENDS OpenAddressingModel

abs(number) == IF number < 0 THEN -1 * number ELSE number

FindOrPut == evict = FALSE

containedInTable(f) == \E l \in 0..L: table[idx(abs(f), l)] = f

Consistent == FindOrPut => \A seen \in history:
            /\ containedInTable(seen) => ~containsElem(external, seen)
            /\ containedInTable(seen * (-1)) => containsElem(external, seen)
            /\ ~containedInTable(seen) => containsElem(external, seen)

=============================================================================
