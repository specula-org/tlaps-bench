------------------------------ MODULE FlashWithMutex_Lemma_3_CorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

Spec == Init /\ [][Next]_vars

Lemma_3 ==
    \A src, dst \in NODE :
        (/\ src # dst /\ dst # Home
         /\ UniMsg[src].Cmd = "UNI_GetX" /\ UniMsg[src].Proc = dst)
            => /\ Dir.Pending /\ ~Dir.Local
               /\ PendReqSrc = src /\ FwdCmd = "UNI_GetX"

=============================================================================
