-----------------MODULE PaxosProof_StructOK1-------------------
EXTENDS TLAPS, PaxosTuple

-----------------------------------------------------------------------------

-----------------------------------------------------------
StructOK1 == \A a \in Acceptor : IF maxVBal[a] = -1
                                 THEN maxVal[a] = None
                                 ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

StructOK1E == \A a \in Acceptor : IF maxVBal[a] = -1
                                  THEN maxVal[a] = None
                                  ELSE \E m \in msgs :
                                         /\ m[1] = "2b"
                                         /\ m[2] = a
                                         /\ m[3] = maxVBal[a]
                                         /\ m[4] = maxVal[a]

IndInv == TypeOK /\ StructOK1E

LEMMA MinusOneNotBallot == -1 \notin Ballot
PROOF
  BY SMT DEF Ballot

LEMMA StructOK1EImpliesStructOK1 == StructOK1E => StructOK1
PROOF
  BY SMT DEF StructOK1E, StructOK1, votes

THEOREM Spec => []StructOK1
PROOF
<1>1. Init => IndInv
  BY SMT DEF Init, IndInv, TypeOK, StructOK1E, Message, Ballot
<1>2. IndInv /\ [Next]_vars => IndInv'
  BY SMT, MinusOneNotBallot
     DEF IndInv, TypeOK, StructOK1E, Next, Phase1a, Phase1b, Phase2a, Phase2b,
         Send, Message, Ballot, vars
<1>3. Spec => []IndInv
  BY <1>1, <1>2, PTL DEF Spec
<1>4. []IndInv => []StructOK1
  BY StructOK1EImpliesStructOK1, PTL DEF IndInv
<1>5. QED
  BY <1>3, <1>4
-----------------------------------------------------------

-----------------------------------------------------------------------------

------------------------------------------------------------
============================================================
