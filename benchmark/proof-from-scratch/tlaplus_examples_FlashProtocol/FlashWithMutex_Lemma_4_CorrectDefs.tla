------------------------------ MODULE FlashWithMutex_Lemma_4_CorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

Spec == Init /\ [][Next]_vars

Lemma_4 ==
    \A p \in NODE :
        (p # Home /\ InvMsg[p].Cmd = "INV_InvAck") =>
            /\ Dir.Pending /\ Collecting
            /\ NakcMsg.Cmd = "NAKC_None" /\ ShWbMsg.Cmd = "SHWB_None"
            /\ \A q \in NODE :
                 /\ (UniMsg[q].Cmd \in {"UNI_Get", "UNI_GetX"} => UniMsg[q].Proc = Home)
                 /\ (UniMsg[q].Cmd = "UNI_PutX" => (UniMsg[q].Proc = Home /\ PendReqSrc = q))

=============================================================================
