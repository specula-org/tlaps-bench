-----------------MODULE PaxosProof_StructOK1Defs-------------------
EXTENDS TLAPS, PaxosTuple

StructOK1 == \A a \in Acceptor : IF maxVBal[a] = -1
                                 THEN maxVal[a] = None
                                 ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

============================================================
