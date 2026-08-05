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
    \/ ABS_NI_Remote_Get_Nak_dst(n)  \/ ABS_NI_Remote_GetX_Nak_dst(n)
    \/ ABS_NI_Remote_Get_Put_dst(n)  \/ ABS_NI_Remote_GetX_PutX_dst(n)

HandleInv(n) == NI_Inv(n) \/ NI_InvAck(n)

HandleShWb == NI_FAck \/ NI_ShWb \/ ABS_NI_ShWb

AbsRespond(d) ==
    \/ ABS_NI_Remote_Nak_src(d)
    \/ ABS_NI_Remote_Get_Put_src(d)
    \/ ABS_NI_Remote_GetX_PutX_src(d)

AbsRespondSrcDst ==
    \/ ABS_NI_Remote_Nak_src_dst
    \/ ABS_NI_Remote_Get_Put_src_dst
    \/ ABS_NI_Remote_GetX_PutX_src_dst

Fairness ==
    /\ \A n \in NODE : /\ WF_vars(HandleUni(n))
                       /\ WF_vars(HandleInv(n))
                       /\ WF_vars(NI_Replace(n))
                       /\ WF_vars(AbsRespond(n))
    /\ WF_vars(NI_Nak_Clear)
    /\ WF_vars(NI_Wb)
    /\ WF_vars(HandleShWb)
    /\ WF_vars(ABS_NI_InvAck)
    /\ WF_vars(AbsRespondSrcDst)

FairSpec == Init /\ [][Next]_vars /\ Fairness

ShWbProgress == (ShWbMsg.Cmd # "SHWB_None") ~> (ShWbMsg.Cmd = "SHWB_None")

=============================================================================
