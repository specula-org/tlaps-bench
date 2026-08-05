------------------------------ MODULE FlashWithMutex_Lemma_2_CorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

Spec == Init /\ [][Next]_vars

Lemma_2 ==
    \A src, dst \in NODE :
        (/\ src # dst /\ dst # Home
         /\ UniMsg[src].Cmd = "UNI_Get" /\ UniMsg[src].Proc = dst)
            => /\ Dir.Pending /\ ~Dir.Local
               /\ PendReqSrc = src /\ FwdCmd = "UNI_Get"

=============================================================================
