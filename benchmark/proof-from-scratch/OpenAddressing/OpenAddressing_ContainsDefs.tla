

-------------------------- MODULE OpenAddressing_ContainsDefs --------------------------
EXTENDS OpenAddressingModel

contains(f,t,seq,Q) == \/ \E i \in 0..Q: isMatch(f,idx(f,i),t)
                       \/ \E i \in 1..Len(seq): seq[i] = f
                       \/ IF f \in ({ lo[x] : x \in DOMAIN lo } \ {0}) THEN evict = TRUE
                                                     ELSE FALSE

Contains == /\ \A seen \in history: 
                           contains(seen,table,external,L)
            /\ \A unseen \in (fps \ history):
                          ~contains(unseen,table,external,L)

=============================================================================
