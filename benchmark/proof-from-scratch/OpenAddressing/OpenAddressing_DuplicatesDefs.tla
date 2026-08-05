

-------------------------- MODULE OpenAddressing_DuplicatesDefs --------------------------
EXTENDS OpenAddressingModel

abs(number) == IF number < 0 THEN -1 * number ELSE number

FindOrPut == evict = FALSE

Duplicates == FindOrPut => \A i \in 1..K : \A j \in (i+1)..K :
                 (table[i] # empty /\ table[j] # empty) => abs(table[i]) # abs(table[j])

=============================================================================
