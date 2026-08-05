------------------------------ MODULE FlashWithMutex_Lemma_5_Correct ------------------------------

EXTENDS FlashWithMutex

Spec == Init /\ [][Next]_vars

Lemma_5 ==
    \A p \in NODE : Proc[p].CacheState = "CACHE_E" => Proc[p].CacheData = CurrData
THEOREM Lemma_5_Correct == Spec => []Lemma_5
PROOF OBVIOUS
=============================================================================
