------------------------------ MODULE FlashWithMutex_Lemma_1_CorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

Spec == Init /\ [][Next]_vars

Lemma_1 ==
    \A dst \in NODE :
        Proc[dst].CacheState = "CACHE_E" =>
            /\ Dir.Dirty
            /\ WbMsg.Cmd # "WB_Wb"
            /\ ShWbMsg.Cmd # "SHWB_ShWb"
            /\ \A p \in NODE : p # dst => Proc[p].CacheState # "CACHE_E"
            /\ UniMsg[Home].Cmd # "UNI_Put"
            /\ \A q \in NODE : UniMsg[q].Cmd # "UNI_PutX"

=============================================================================
