------------------------------ MODULE FlashWithMutex_CacheDataCorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

Spec == Init /\ [][Next]_vars

CacheDataProp ==
    \A p \in NODE :
        /\ (Proc[p].CacheState = "CACHE_E" => Proc[p].CacheData = CurrData)
        /\ (Proc[p].CacheState = "CACHE_S" =>
              /\ (Collecting => Proc[p].CacheData = PrevData)
              /\ (~Collecting => Proc[p].CacheData = CurrData))

=============================================================================
