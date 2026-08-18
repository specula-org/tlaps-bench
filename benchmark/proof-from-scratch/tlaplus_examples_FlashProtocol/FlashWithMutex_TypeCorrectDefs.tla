------------------------------ MODULE FlashWithMutex_TypeCorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

CACHE_STATE == {"CACHE_I", "CACHE_S", "CACHE_E"}
NODE_CMD    == {"NODE_None", "NODE_Get", "NODE_GetX"}
UNI_CMD     == {"UNI_None", "UNI_Get", "UNI_GetX", "UNI_Put", "UNI_PutX", "UNI_Nak"}
INV_CMD     == {"INV_None", "INV_Inv", "INV_InvAck"}
RP_CMD      == {"RP_None", "RP_Replace"}
WB_CMD      == {"WB_None", "WB_Wb"}
SHWB_CMD    == {"SHWB_None", "SHWB_ShWb", "SHWB_FAck"}
NAKC_CMD    == {"NAKC_None", "NAKC_Nakc"}

DataU  == DATA \cup {Undefined}
NodeU  == NODE \cup {Undefined}
UniU   == UNI_CMD \cup {Undefined}

TypeOK ==
    /\ Home \in NODE
    /\ Proc \in [NODE -> [ProcCmd : NODE_CMD, InvMarked : BOOLEAN,
                          CacheState : CACHE_STATE, CacheData : DataU]]
    /\ Dir \in [Pending : BOOLEAN, Local : BOOLEAN, Dirty : BOOLEAN,
                HeadVld : BOOLEAN, HeadPtr : NodeU, ShrVld : BOOLEAN,
                ShrSet : SUBSET NODE, InvSet : SUBSET NODE]
    /\ MemData \in DATA
    /\ UniMsg \in [NODE -> [Cmd : UNI_CMD, Proc : NodeU, Data : DataU]]
    /\ InvMsg \in [NODE -> [Cmd : INV_CMD]]
    /\ RpMsg  \in [NODE -> [Cmd : RP_CMD]]
    /\ WbMsg   \in [Cmd : WB_CMD, Proc : NodeU, Data : DataU]
    /\ ShWbMsg \in [Cmd : SHWB_CMD, Proc : NodeU, Data : DataU]
    /\ NakcMsg \in [Cmd : NAKC_CMD]
    /\ CurrData \in DATA
    /\ PrevData \in DATA
    /\ PendReqSrc \in NodeU
    /\ PendReqCmd \in UniU
    /\ Collecting \in BOOLEAN
    /\ FwdCmd \in UNI_CMD
    /\ FwdSrc \in NodeU

Spec == Init /\ [][Next]_vars

=============================================================================
