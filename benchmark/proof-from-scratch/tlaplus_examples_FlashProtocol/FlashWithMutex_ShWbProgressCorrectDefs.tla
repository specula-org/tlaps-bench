------------------------------ MODULE FlashWithMutex_ShWbProgressCorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

HandleUni(n) ==
    \/ NI_Nak(n)
    \/ NI_Local_Get_Nak(n)  \/ NI_Local_Get_Get(n)   \/ NI_Local_Get_Put(n)
    \/ NI_Local_GetX_Nak(n) \/ NI_Local_GetX_GetX(n) \/ NI_Local_GetX_PutX(n)
    \/ NI_Remote_Put(n) \/ NI_Remote_PutX(n)
    \/ (n = Home /\ (NI_Local_Put \/ NI_Local_PutXAcksDone))
    \/ \E d \in NODE : \/ NI_Remote_Nak(n, d)
                       \/ NI_Remote_Get_Put(n, d)
                       \/ NI_Remote_GetX_PutX(n, d)

HandleInv(n) == NI_Inv(n) \/ NI_InvAck(n)

HandleShWb == NI_FAck \/ NI_ShWb

Fairness ==
    /\ \A n \in NODE : /\ WF_vars(HandleUni(n))
                       /\ WF_vars(HandleInv(n))
                       /\ WF_vars(NI_Replace(n))
    /\ WF_vars(NI_Nak_Clear)
    /\ WF_vars(NI_Wb)
    /\ WF_vars(HandleShWb)

FairSpec == Init /\ [][Next]_vars /\ Fairness

ShWbProgress == (ShWbMsg.Cmd # "SHWB_None") ~> (ShWbMsg.Cmd = "SHWB_None")

=============================================================================
