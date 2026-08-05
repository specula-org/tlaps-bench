------------------------------ MODULE FlashWithMutex_Lemma_3_Correct ------------------------------

EXTENDS FlashWithMutex

Spec == Init /\ [][Next]_vars

Lemma_3 ==
    \A src, dst \in NODE :
        (/\ src # dst /\ dst # Home
         /\ UniMsg[src].Cmd = "UNI_GetX" /\ UniMsg[src].Proc = dst)
            => /\ Dir.Pending /\ ~Dir.Local
               /\ PendReqSrc = src /\ FwdCmd = "UNI_GetX"
THEOREM Lemma_3_Correct == Spec => []Lemma_3
PROOF OBVIOUS

=============================================================================
