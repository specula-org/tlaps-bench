------------------------------ MODULE FlashWithMutex_CacheStateCorrect ------------------------------

EXTENDS FlashWithMutex

Spec == Init /\ [][Next]_vars

CacheStateProp ==
    \A p, q \in NODE :
        p # q => ~(Proc[p].CacheState = "CACHE_E" /\ Proc[q].CacheState = "CACHE_E")
THEOREM CacheStateCorrect == Spec => []CacheStateProp
PROOF OBVIOUS

=============================================================================
