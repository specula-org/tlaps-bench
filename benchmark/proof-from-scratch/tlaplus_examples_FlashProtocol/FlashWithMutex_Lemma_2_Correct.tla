------------------------------ MODULE FlashWithMutex_Lemma_2_Correct ------------------------------

EXTENDS FlashWithMutex

Spec == Init /\ [][Next]_vars

Lemma_2 ==
    \A src, dst \in NODE :
        (/\ src # dst /\ dst # Home
         /\ UniMsg[src].Cmd = "UNI_Get" /\ UniMsg[src].Proc = dst)
            => /\ Dir.Pending /\ ~Dir.Local
               /\ PendReqSrc = src /\ FwdCmd = "UNI_Get"
THEOREM Lemma_2_Correct == Spec => []Lemma_2
PROOF OBVIOUS

=============================================================================
