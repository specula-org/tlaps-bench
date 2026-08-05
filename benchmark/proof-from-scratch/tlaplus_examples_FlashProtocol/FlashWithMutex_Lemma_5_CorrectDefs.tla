------------------------------ MODULE FlashWithMutex_Lemma_5_CorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

Spec == Init /\ [][Next]_vars

Lemma_5 ==
    \A p \in NODE : Proc[p].CacheState = "CACHE_E" => Proc[p].CacheData = CurrData
=============================================================================
