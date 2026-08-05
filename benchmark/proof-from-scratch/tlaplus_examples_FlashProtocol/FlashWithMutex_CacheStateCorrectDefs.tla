------------------------------ MODULE FlashWithMutex_CacheStateCorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

Spec == Init /\ [][Next]_vars

CacheStateProp ==
    \A p, q \in NODE :
        p # q => ~(Proc[p].CacheState = "CACHE_E" /\ Proc[q].CacheState = "CACHE_E")

=============================================================================
