

-------------------------- MODULE OpenAddressing_SortedDefs --------------------------
EXTENDS OpenAddressingModel

isSorted(seq) == LET sub == SelectSeq(seq, LAMBDA e: e # empty)
                 IN IF Len(sub) < 2 THEN TRUE
                    ELSE \A i \in 1..(Len(sub) - 1):
                            sub[i] < sub[i+1]

Sorted == isSorted(external) /\ isSorted(newexternal)

=============================================================================
